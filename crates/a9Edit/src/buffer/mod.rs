// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! A text buffer for a text editor.
//!
//! Implements a Unicode-aware, layout-aware text buffer for terminals.
//! It's based on a gap buffer. It has no line cache and instead relies
//! on the performance of the ucd module for fast text navigation.
//!
//! ---
//!
//! If the project ever outgrows a basic gap buffer (e.g. to add time travel)
//! an ideal, alternative architecture would be a piece table with immutable trees.
//! The tree nodes can be allocated on the same arena allocator as the added chunks,
//! making lifetime management fairly easy. The algorithm is described here:
//! * <https://cdacamar.github.io/data%20structures/algorithms/benchmarking/text%20editors/c++/editor-data-structures/>
//! * <https://github.com/cdacamar/fredbuf>
//!
//! The downside is that text navigation & search takes a performance hit due to small chunks.
//! The solution to the former is to keep line caches, which further complicates the architecture.
//! There's no solution for the latter. However, there's a chance that the performance will still be sufficient.

mod forbidden;
mod gap_buffer;
mod navigation;
mod ruby;

pub use forbidden::ForbiddenRules;

use std::borrow::Cow;
use std::cell::UnsafeCell;
use std::collections::VecDeque;
use std::fs::File;
use std::io::{self, Read as _, Write as _};
use std::mem::{self, MaybeUninit};
use std::ops::Range;
use std::rc::Rc;
use std::str;

pub use gap_buffer::GapBuffer;
use stdext::arena::{Arena, scratch_arena};
use stdext::collections::{BString, BVec};
use stdext::{ReplaceRange as _, arena_write_fmt, minmax, slice_as_uninit_mut, slice_copy_safe};

use crate::cell::SemiRefCell;
use crate::clipboard::Clipboard;
use crate::document::{ReadableDocument, WriteableDocument};
use crate::framebuffer::{Attributes, Framebuffer, IndexedColor};
use crate::helpers::*;
use crate::lsh::cache::HighlighterCache;
use crate::lsh::{HighlightKind, Highlighter, Language};
use crate::oklab::StraightRgba;
use crate::simd::memchr2;
use crate::unicode::{self, Cursor, HiddenText, MeasurementConfig};
use crate::{icu, simd};

/// The margin template is used for line numbers.
/// The max. line number we should ever expect is probably 64-bit,
/// and so this template fits 19 digits, followed by " │ ".
const MARGIN_TEMPLATE: &[u8] = "                    │ ".as_bytes();
/// Just a bunch of whitespace you can use for turning tabs into spaces.
/// Happens to reuse MARGIN_TEMPLATE, because it has sufficient whitespace.
const TAB_WHITESPACE: &[u8] = MARGIN_TEMPLATE;
const VISUAL_SPACE: &[u8] = "･".as_bytes();
const VISUAL_SPACE_PREFIX_ADD: usize = '･'.len_utf8() - 1;
const VISUAL_TAB: &[u8] = "￫       ".as_bytes();
const VISUAL_TAB_PREFIX_ADD: usize = '￫'.len_utf8() - 1;

pub enum IoError {
    Io(io::Error),
    Icu(icu::Error),
}

pub type IoResult<T> = std::result::Result<T, IoError>;

impl From<io::Error> for IoError {
    fn from(err: io::Error) -> Self {
        Self::Io(err)
    }
}

impl From<icu::Error> for IoError {
    fn from(err: icu::Error) -> Self {
        Self::Icu(err)
    }
}

/// Stores statistics about the whole document.
#[derive(Copy, Clone)]
pub struct TextBufferStatistics {
    logical_lines: CoordType,
    visual_lines: CoordType,
}

/// Stores the active text selection anchors.
///
/// The two points are not sorted. Instead, `beg` refers to where the selection
/// started being made and `end` refers to the currently being updated position.
#[derive(Copy, Clone)]
struct TextBufferSelection {
    beg: Point,
    end: Point,
}

/// In order to group actions into a single undo step,
/// we need to know the type of action that was performed.
/// This stores the action type.
#[derive(Copy, Clone, Eq, PartialEq)]
enum HistoryType {
    Other,
    Write,
    Delete,
}

/// An undo/redo entry.
struct HistoryEntry {
    /// [`TextBuffer::cursor`] position before the change was made.
    cursor_before: Point,
    /// [`TextBuffer::selection`] before the change was made.
    selection_before: Option<TextBufferSelection>,
    /// [`TextBuffer::stats`] before the change was made.
    stats_before: TextBufferStatistics,
    /// [`GapBuffer::generation`] before the change was made.
    ///
    /// **NOTE:** Entries with the same generation are grouped together.
    generation_before: u32,
    /// Logical cursor position where the change took place.
    /// The position is at the start of the changed range.
    cursor: Point,
    /// Text that was deleted from the buffer.
    deleted: Vec<u8>,
    /// Text that was added to the buffer.
    added: Vec<u8>,
    /// Soft wrap boundaries saved while editing visible formatting source.
    format_wraps_before: Option<Vec<usize>>,
}

/// Caches an ICU search operation.
struct ActiveSearch {
    /// The search pattern.
    pattern: String,
    /// The search options.
    options: SearchOptions,
    /// The ICU `UText` object.
    text: icu::Text,
    /// The ICU `URegularExpression` object.
    regex: icu::Regex,
    /// [`GapBuffer::generation`] when the search was created.
    /// This is used to detect if we need to refresh the
    /// [`ActiveSearch::regex`] object.
    buffer_generation: u32,
    /// [`TextBuffer::selection_generation`] when the search was
    /// created. When the user manually selects text, we need to
    /// refresh the [`ActiveSearch::pattern`] with it.
    selection_generation: u32,
    /// Stores the text buffer offset in between searches.
    next_search_offset: usize,
    /// If we know there were no hits, we can skip searching.
    no_matches: bool,
}

/// Options for a search operation.
#[derive(Default, Clone, Copy, Eq, PartialEq)]
pub struct SearchOptions {
    /// If true, the search is case-sensitive.
    pub match_case: bool,
    /// If true, the search matches whole words.
    pub whole_word: bool,
    /// If true, the search uses regex.
    pub use_regex: bool,
}

enum RegexReplacement<'a> {
    Group(i32),
    Text(BVec<'a, u8>),
}

/// Caches the start and length of the active edit line for a single edit.
/// This helps us avoid having to remeasure the buffer after an edit.
struct ActiveEditLineInfo {
    /// Points to the start of the currently being edited line.
    safe_start: Cursor,
    /// Number of visual rows of the line that starts
    /// at [`ActiveEditLineInfo::safe_start`].
    line_height_in_rows: CoordType,
    /// Byte distance from the start of the line at
    /// [`ActiveEditLineInfo::safe_start`] to the next line.
    distance_next_line_start: usize,
}

/// Undo/redo grouping works by recording a set of "overrides",
/// which are then applied in [`TextBuffer::edit_begin()`].
/// This allows us to create a group of edits that all share a
/// common `generation_before` and can be undone/redone together.
/// This struct stores those overrides.
struct ActiveEditGroupInfo {
    /// [`TextBuffer::cursor`] position before the change was made.
    cursor_before: Point,
    /// [`TextBuffer::selection`] before the change was made.
    selection_before: Option<TextBufferSelection>,
    /// [`TextBuffer::stats`] before the change was made.
    stats_before: TextBufferStatistics,
    /// [`GapBuffer::generation`] before the change was made.
    ///
    /// **NOTE:** Entries with the same generation are grouped together.
    generation_before: u32,
}

/// Char- or word-wise navigation? Your choice.
pub enum CursorMovement {
    Grapheme,
    Word,
}

/// See [`TextBuffer::move_selected_lines`].
pub enum MoveLineDirection {
    Up,
    Down,
}

/// The result of a call to [`TextBuffer::render()`].
pub struct RenderResult {
    /// The maximum visual X position we encountered during rendering.
    pub visual_pos_x_max: CoordType,
}

/// A [`TextBuffer`] with inner mutability.
pub type TextBufferCell = SemiRefCell<TextBuffer>;

/// A [`TextBuffer`] inside an [`Rc`].
///
/// We need this because the TUI system needs to borrow
/// the given text buffer(s) until after the layout process.
pub type RcTextBuffer = Rc<TextBufferCell>;

/// A text buffer for a text editor.
struct FormatEdit {
    source: Range<usize>,
    wraps: Vec<usize>,
    wrap_column: CoordType,
    undo_floor: usize,
    undone: usize,
}

impl FormatEdit {
    fn replace(&mut self, replaced: Range<usize>, added: usize) {
        let adjust = |offset: usize| {
            if offset < replaced.start {
                offset
            } else if offset <= replaced.end {
                replaced.start + added
            } else {
                offset - replaced.len() + added
            }
        };
        self.source.end = adjust(self.source.end);
        for offset in &mut self.wraps {
            if *offset != replaced.start {
                *offset = adjust(*offset);
            }
        }
        self.wraps.retain(|&offset| offset > self.source.start && offset < self.source.end);
        self.wraps.dedup();
    }
}

pub struct TextBuffer {
    buffer: GapBuffer,

    undo_stack: VecDeque<SemiRefCell<HistoryEntry>>,
    redo_stack: VecDeque<SemiRefCell<HistoryEntry>>,
    last_history_type: HistoryType,
    last_save_generation: u32,

    active_edit_group: Option<ActiveEditGroupInfo>,
    active_edit_line_info: Option<ActiveEditLineInfo>,
    active_edit_depth: i32,
    active_edit_off: usize,

    stats: TextBufferStatistics,
    cursor: Cursor,
    // When scrolling significant amounts of text away from the cursor,
    // rendering will naturally slow down proportionally to the distance.
    // To avoid this, we cache the cursor position for rendering.
    // Must be cleared on every edit or reflow.
    cursor_for_rendering: Option<Cursor>,
    selection: Option<TextBufferSelection>,
    selection_latch: Option<Point>,
    selection_generation: u32,
    search: Option<UnsafeCell<ActiveSearch>>,
    highlighter_cache: HighlighterCache,
    ruby_cache: ruby::RubyCache,
    ruby_display: bool,
    format_edit: Option<FormatEdit>,
    forbidden_rules: Option<Rc<ForbiddenRules>>,
    warning_cache: std::cell::RefCell<forbidden::WarningCache>,

    width: CoordType,
    margin_width: CoordType,
    margin_enabled: bool,
    word_wrap_column: CoordType,
    wrap_chars: Option<CoordType>,
    word_wrap_enabled: bool,
    tab_size: CoordType,
    indent_with_tabs: bool,
    line_highlight_enabled: bool,
    language: Option<&'static Language>,
    ruler: CoordType,
    encoding: &'static str,
    newlines_are_crlf: bool,
    insert_final_newline: bool,
    overtype: bool,

    wants_cursor_visibility: bool,
}

impl TextBuffer {
    /// Creates a new text buffer inside an [`Rc`].
    /// See [`TextBuffer::new()`].
    pub fn new_rc(small: bool) -> io::Result<RcTextBuffer> {
        let buffer = Self::new(small)?;
        Ok(Rc::new(SemiRefCell::new(buffer)))
    }

    /// Creates a new text buffer. With `small` you can control
    /// if the buffer is optimized for <1MiB contents.
    pub fn new(small: bool) -> io::Result<Self> {
        Ok(Self {
            buffer: GapBuffer::new(small)?,

            undo_stack: Default::default(),
            redo_stack: Default::default(),
            last_history_type: HistoryType::Other,
            last_save_generation: 0,

            active_edit_group: None,
            active_edit_line_info: None,
            active_edit_depth: 0,
            active_edit_off: 0,

            stats: TextBufferStatistics { logical_lines: 1, visual_lines: 1 },
            cursor: Default::default(),
            cursor_for_rendering: None,
            selection: None,
            selection_latch: None,
            selection_generation: 0,
            search: None,
            highlighter_cache: HighlighterCache::new(),
            ruby_cache: ruby::RubyCache::default(),
            ruby_display: false,
            format_edit: None,
            forbidden_rules: None,
            warning_cache: Default::default(),

            width: 0,
            margin_width: 0,
            margin_enabled: false,
            word_wrap_column: 0,
            wrap_chars: None,
            word_wrap_enabled: false,
            tab_size: 4,
            indent_with_tabs: false,
            line_highlight_enabled: false,
            language: None,
            ruler: 0,
            encoding: "UTF-8",
            newlines_are_crlf: cfg!(windows), // Windows users want CRLF
            insert_final_newline: false, // NOTE: Even with POSIX, single-line buffers need this to be false
            overtype: false,

            wants_cursor_visibility: false,
        })
    }

    /// Length of the document in bytes.
    pub fn text_length(&self) -> usize {
        self.buffer.len()
    }

    /// Number of logical lines in the document,
    /// that is, lines separated by newlines.
    pub fn logical_line_count(&self) -> CoordType {
        self.stats.logical_lines
    }

    /// Number of visual lines in the document,
    /// that is, the number of lines after layout.
    pub fn visual_line_count(&self) -> CoordType {
        self.stats.visual_lines
    }

    /// Does the buffer need to be saved?
    pub fn is_dirty(&self) -> bool {
        self.last_save_generation != self.buffer.generation()
    }

    /// The buffer generation changes on every edit.
    /// With this you can check if it has changed since
    /// the last time you called this function.
    pub fn generation(&self) -> u32 {
        self.buffer.generation()
    }

    /// Force the buffer to be dirty (needs to be saved to disk).
    pub fn mark_as_dirty(&mut self) {
        self.last_save_generation = self.buffer.generation().wrapping_sub(1);
    }

    /// Force the buffer to be clean (has been saved to disk).
    /// Use this with caution. It's called automatically on write().
    pub fn mark_as_clean(&mut self) {
        self.last_save_generation = self.buffer.generation();
    }

    /// The encoding used during reading/writing. "UTF-8" is the default.
    pub fn encoding(&self) -> &'static str {
        self.encoding
    }

    /// Set the encoding used during reading/writing.
    pub fn set_encoding(&mut self, encoding: &'static str) {
        if self.encoding != encoding {
            self.encoding = encoding;
            self.mark_as_dirty();
        }
    }

    /// The newline type used in the document. LF or CRLF.
    pub fn is_crlf(&self) -> bool {
        self.newlines_are_crlf
    }

    /// Changes the newline type without normalizing the document.
    pub fn set_crlf(&mut self, crlf: bool) {
        self.newlines_are_crlf = crlf;
    }

    /// Changes the newline type used in the document.
    ///
    /// NOTE: Cannot be undone.
    pub fn normalize_newlines(&mut self, crlf: bool) {
        if self.is_format_editing() {
            return;
        }
        let newline: &[u8] = if crlf { b"\r\n" } else { b"\n" };
        let mut off = 0;

        let mut cursor_offset = self.cursor.offset;
        let mut cursor_for_rendering_offset =
            self.cursor_for_rendering.map_or(cursor_offset, |c| c.offset);

        #[cfg(debug_assertions)]
        let mut adjusted_newlines = 0;

        'outer: loop {
            // Seek to the offset of the next line start.
            loop {
                let chunk = self.read_forward(off);
                if chunk.is_empty() {
                    break 'outer;
                }

                let (delta, line) = simd::lines_fwd(chunk, 0, 0, 1);
                off += delta;
                if line == 1 {
                    break;
                }
            }

            // Get the preceding newline.
            let chunk = self.read_backward(off);
            let chunk_newline_len = if chunk.ends_with(b"\r\n") { 2 } else { 1 };
            let chunk_newline = &chunk[chunk.len() - chunk_newline_len..];

            if chunk_newline != newline {
                // If this newline is still before our cursor position, then it still has an effect on its offset.
                // Any newline adjustments past that cursor position are irrelevant.
                let delta = newline.len() as isize - chunk_newline_len as isize;
                if off <= cursor_offset {
                    cursor_offset = cursor_offset.saturating_add_signed(delta);
                    #[cfg(debug_assertions)]
                    {
                        adjusted_newlines += 1;
                    }
                }
                if off <= cursor_for_rendering_offset {
                    cursor_for_rendering_offset =
                        cursor_for_rendering_offset.saturating_add_signed(delta);
                }

                // Replace the newline.
                off -= chunk_newline_len;
                self.buffer.replace(off..off + chunk_newline_len, newline);
                off += newline.len();
            }
        }

        // If this fails, the cursor offset calculation above is wrong.
        #[cfg(debug_assertions)]
        debug_assert_eq!(adjusted_newlines, self.cursor.logical_pos.y);

        self.cursor.offset = cursor_offset;
        if let Some(cursor) = &mut self.cursor_for_rendering {
            cursor.offset = cursor_for_rendering_offset;
        }

        self.newlines_are_crlf = crlf;
    }

    /// If enabled, automatically insert a final newline
    /// when typing at the end of the file.
    pub fn set_insert_final_newline(&mut self, enabled: bool) {
        self.insert_final_newline = enabled;
    }

    /// Whether to insert or overtype text when writing.
    pub fn is_overtype(&self) -> bool {
        self.overtype
    }

    /// Set the overtype mode.
    pub fn set_overtype(&mut self, overtype: bool) {
        self.overtype = overtype;
    }

    /// Gets the logical cursor position, that is,
    /// the position in lines and graphemes per line.
    pub fn cursor_logical_pos(&self) -> Point {
        self.cursor.logical_pos
    }

    /// Gets the visual cursor position, that is,
    /// the position in laid out rows and columns.
    pub fn cursor_visual_pos(&self) -> Point {
        self.cursor.visual_pos
    }

    /// Gets the width of the left margin.
    pub fn margin_width(&self) -> CoordType {
        self.margin_width
    }

    /// Is the left margin enabled?
    pub fn set_margin_enabled(&mut self, enabled: bool) -> bool {
        if self.margin_enabled == enabled {
            false
        } else {
            self.margin_enabled = enabled;
            self.reflow();
            true
        }
    }

    /// Gets the width of the text contents for layout.
    pub fn text_width(&self) -> CoordType {
        self.width - self.margin_width
    }

    /// Ask the TUI system to scroll the buffer and make the cursor visible.
    ///
    /// TODO: This function shows that [`TextBuffer`] is poorly abstracted
    /// away from the TUI system. The only reason this exists is so that
    /// if someone outside the TUI code enables word-wrap, the TUI code
    /// recognizes this and scrolls the cursor into view. But outside of this
    /// scrolling, views, etc., are all UI concerns = this should not be here.
    pub fn make_cursor_visible(&mut self) {
        self.wants_cursor_visibility = true;
    }

    /// For the TUI code to retrieve a prior [`TextBuffer::make_cursor_visible()`] request.
    pub fn take_cursor_visibility_request(&mut self) -> bool {
        mem::take(&mut self.wants_cursor_visibility)
    }

    /// Is word-wrap enabled?
    ///
    /// Technically, this is a misnomer, because it's line-wrapping.
    pub fn is_word_wrap_enabled(&self) -> bool {
        self.word_wrap_enabled
    }

    /// Enable or disable word-wrap.
    ///
    /// NOTE: It's expected that the tui code calls `set_width()` sometime after this.
    /// This will then trigger the actual recalculation of the cursor position.
    pub fn set_word_wrap(&mut self, enabled: bool) {
        if self.is_format_editing() {
            return;
        }
        if self.word_wrap_enabled != enabled {
            self.word_wrap_enabled = enabled;
            self.width = 0; // Force a reflow.
            self.make_cursor_visible();
        }
    }

    /// The configured wrap limit in full-width Japanese characters.
    /// Half-width characters occupy half a character; None follows the viewport.
    pub fn wrap_chars(&self) -> Option<CoordType> {
        self.wrap_chars
    }

    /// Set the wrap limit in full-width Japanese characters.
    pub fn set_wrap_chars(&mut self, count: Option<CoordType>) {
        let count = count.map(|count| count.clamp(1, CoordType::MAX / 2));
        if self.wrap_chars != count {
            self.wrap_chars = count;
            self.reflow();
            self.make_cursor_visible();
        }
    }

    /// Show ruby/emphasis bases, preserving the original markup for editing and saving.
    pub fn set_ruby_display(&mut self, enabled: bool) {
        if !enabled && self.is_format_editing() {
            self.toggle_format_editing();
        }
        if self.ruby_display != enabled {
            self.ruby_display = enabled;
            self.reflow();
            self.make_cursor_visible();
        }
    }

    fn ruby_line(&self, offset: usize) -> Rc<ruby::Line> {
        self.ruby_cache.prepare(self.buffer.generation());
        self.ruby_cache.line(&self.buffer, offset)
    }

    pub fn is_format_editing(&self) -> bool {
        self.format_edit.is_some()
    }

    /// Toggle source editing for the annotated logical line under the caret.
    pub fn toggle_format_editing(&mut self) -> bool {
        if self.format_edit.is_some() {
            self.format_edit = None;
            self.search = None;
            self.clear_selection();
            self.last_history_type = HistoryType::Other;
            self.reflow();
            self.cursor = self.skip_hidden_ruby(self.cursor, 1);
            self.make_cursor_visible();
            return true;
        }
        if !self.ruby_display
            || !self
                .ruby_line(self.cursor.offset)
                .ruby
                .iter()
                .any(|ruby| (ruby.markup.start..ruby.base.end).contains(&self.cursor.offset))
        {
            return false;
        }
        let start = self.goto_line_start(self.cursor, self.cursor.logical_pos.y);
        let end = self.cursor_move_to_logical_internal(
            start,
            Point { x: CoordType::MAX, y: start.logical_pos.y },
        );
        let mut wraps = Vec::new();
        for y in start.visual_pos.y + 1..=end.visual_pos.y {
            let row = self.cursor_move_to_visual_internal(start, Point { x: 0, y });
            if row.offset > start.offset && row.offset < end.offset {
                wraps.push(self.ruby_insertion_cursor(row).offset);
            }
        }
        self.clear_selection();
        self.search = None;
        self.last_history_type = HistoryType::Other;
        self.format_edit = Some(FormatEdit {
            source: start.offset..end.offset,
            wraps,
            wrap_column: self.word_wrap_column,
            undo_floor: self.undo_stack.len(),
            undone: 0,
        });
        self.reflow();
        self.make_cursor_visible();
        true
    }

    fn source_is_visible(&self, offset: usize) -> bool {
        self.format_edit
            .as_ref()
            .is_some_and(|edit| edit.source.start <= offset && offset <= edit.source.end)
    }

    fn constrain_format_cursor(&self, cursor: Cursor) -> Cursor {
        if let Some(edit) = &self.format_edit {
            let offset = cursor.offset.clamp(edit.source.start, edit.source.end);
            if offset != cursor.offset {
                return self.cursor_move_to_offset_internal(self.cursor, offset);
            }
        }
        cursor
    }

    fn update_format_offsets(&mut self, replaced: Range<usize>, added: usize) {
        if let Some(edit) = &mut self.format_edit {
            edit.replace(replaced, added);
        }
    }

    /// Reading of the ruby base at the caret, if any.
    pub fn ruby_reading_at_cursor(&self) -> Option<String> {
        if !self.ruby_display {
            return None;
        }
        self.ruby_line(self.cursor.offset)
            .ruby
            .iter()
            .find(|ruby| (ruby.markup.start..ruby.base.end).contains(&self.cursor.offset))
            .and_then(|ruby| match &ruby.kind {
                ruby::AnnotationKind::Ruby(reading) => Some(reading.clone()),
                ruby::AnnotationKind::Emphasis => None,
            })
    }

    /// Annotation of the displayed base at the caret, for the message area.
    pub fn annotation_at_cursor(&self) -> Option<String> {
        if !self.ruby_display {
            return None;
        }
        self.ruby_line(self.cursor.offset)
            .ruby
            .iter()
            .find(|ruby| (ruby.markup.start..ruby.base.end).contains(&self.cursor.offset))
            .map(|ruby| match &ruby.kind {
                ruby::AnnotationKind::Ruby(reading) => format!("ルビ:[{reading}]"),
                ruby::AnnotationKind::Emphasis => "圏点:[﹅]".to_string(),
            })
    }

    pub fn set_forbidden_rules(&mut self, rules: Option<Rc<ForbiddenRules>>) {
        self.forbidden_rules = rules;
        *self.warning_cache.borrow_mut() = Default::default();
    }

    fn forbidden_line_warnings(&self, start: Cursor) -> Rc<Vec<forbidden::Warning>> {
        let key = (self.buffer.generation(), self.word_wrap_column, self.ruby_display);
        {
            let mut cache = self.warning_cache.borrow_mut();
            if cache.key != Some(key) {
                cache.key = Some(key);
                cache.lines.clear();
            }
            if let Some(warnings) = cache.lines.get(&start.offset) {
                return warnings.clone();
            }
        }
        let mut cells = Vec::new();
        if let Some(rules) = &self.forbidden_rules
            && self.word_wrap_column > 0
        {
            let mut cursor = start;
            let mut config = self.measurement_config().with_cursor(start);
            loop {
                let next = config
                    .goto_logical(Point { x: cursor.logical_pos.x + 1, y: cursor.logical_pos.y });
                if next.offset <= cursor.offset || next.logical_pos.y != start.logical_pos.y {
                    break;
                }
                let width = next.column - cursor.column;
                if width > 0 {
                    let mut pos = next.visual_pos;
                    if pos.x == 0 {
                        pos.y -= 1;
                        pos.x = self.word_wrap_column;
                    }
                    pos.x -= width;
                    let mut bytes = Vec::new();
                    self.buffer.extract_raw(cursor.offset..next.offset, &mut bytes, usize::MAX);
                    cells.push(forbidden::Cell {
                        source: cursor.offset..next.offset,
                        text: String::from_utf8_lossy(&bytes).into_owned(),
                        pos,
                        width,
                    });
                }
                cursor = next;
            }
            let bases = if self.ruby_display {
                self.ruby_line(start.offset)
                    .ruby
                    .iter()
                    .filter(|ruby| matches!(ruby.kind, ruby::AnnotationKind::Ruby(_)))
                    .map(|ruby| ruby.base.clone())
                    .collect::<Vec<_>>()
            } else {
                Vec::new()
            };
            let warnings = Rc::new(forbidden::warnings(&cells, rules, &bases));
            self.warning_cache.borrow_mut().lines.insert(start.offset, warnings.clone());
            return warnings;
        }
        Rc::new(Vec::new())
    }

    pub fn forbidden_warning_at_cursor(&self) -> Option<String> {
        if self.forbidden_rules.is_none() || self.word_wrap_column <= 0 {
            return None;
        }
        let cursor = self.skip_hidden_ruby(self.cursor, 1);
        let start = self.goto_line_start(cursor, cursor.logical_pos.y);
        self.forbidden_line_warnings(start)
            .iter()
            .find(|warning| warning.source.contains(&cursor.offset))
            .map(|warning| warning.reasons.join(" "))
    }

    fn hidden_ruby_range(&self, offset: usize) -> Option<Range<usize>> {
        if !self.ruby_display || self.source_is_visible(offset) {
            return None;
        }
        self.ruby_cache.prepare(self.buffer.generation());
        self.ruby_cache.hidden_range(&self.buffer, offset)
    }

    // A caret at the edge of a collapsed annotation inserts outside its markup.
    // Keep navigation/selection offsets unchanged so partial base edits still work.
    fn ruby_insertion_cursor(&self, cursor: Cursor) -> Cursor {
        if self.ruby_display && !self.source_is_visible(cursor.offset) {
            for ruby in &self.ruby_line(cursor.offset).ruby {
                let offset = if (ruby.markup.start..=ruby.base.start).contains(&cursor.offset) {
                    ruby.markup.start
                } else if (ruby.base.end..ruby.markup.end).contains(&cursor.offset) {
                    ruby.markup.end
                } else {
                    continue;
                };
                return self.cursor_move_to_offset_internal(cursor, offset);
            }
        }
        cursor
    }

    // Keep delimiters/readings intact when editing part of a base. Selecting the
    // whole base includes its complete source markup for copy, replacement and deletion.
    fn ruby_source_range(&self, beg: Cursor, end: Cursor) -> (Cursor, Cursor) {
        if self.is_format_editing() {
            return (self.constrain_format_cursor(beg), self.constrain_format_cursor(end));
        }
        if !self.ruby_display {
            return (beg, end);
        }
        let mut start = beg.offset;
        let mut finish = end.offset;
        for offset in [beg.offset, end.offset.saturating_sub(1)] {
            let line = self.ruby_line(offset);
            for ruby in &line.ruby {
                if start <= ruby.base.start
                    && finish >= ruby.base.end
                    && start < ruby.markup.end
                    && finish > ruby.markup.start
                {
                    start = start.min(ruby.markup.start);
                    finish = finish.max(ruby.markup.end);
                    continue;
                }
                if (ruby.markup.start..ruby.base.start).contains(&start) {
                    start = ruby.base.start;
                } else if (ruby.base.end..ruby.markup.end).contains(&start) {
                    start = ruby.markup.end;
                }
                if finish > ruby.base.end && finish <= ruby.markup.end {
                    finish = ruby.base.end;
                } else if finish > ruby.markup.start && finish <= ruby.base.start {
                    finish = ruby.markup.start;
                }
            }
        }
        if start >= finish {
            return (beg, beg);
        }
        let beg = self.cursor_move_to_offset_internal(beg, start);
        (beg, self.cursor_move_to_offset_internal(beg, finish))
    }

    /// Set the width available for layout.
    ///
    /// Ideally this would be a pure UI concern, but the text buffer needs this
    /// so that it can abstract away  visual cursor movement such as "go a line up".
    /// What would that even mean if it didn't know how wide a line is?
    pub fn set_width(&mut self, width: CoordType) -> bool {
        if width <= 0 || width == self.width {
            false
        } else {
            self.width = width;
            self.reflow();
            true
        }
    }

    /// Set the tab width. Could be anything, but is expected to be 1-8.
    pub fn tab_size(&self) -> CoordType {
        self.tab_size
    }

    /// Set the tab size. Clamped to 1-8.
    pub fn set_tab_size(&mut self, width: CoordType) -> bool {
        let width = width.clamp(1, 8);
        if width == self.tab_size {
            false
        } else {
            self.tab_size = width;
            self.reflow();
            true
        }
    }

    /// Calculates the amount of spaces a tab key press would insert at the given column.
    /// This also equals the visual width of an actual tab character.
    ///
    /// This exists because Rust doesn't have range constraints yet, and without
    /// them assembly blows up in size by 7x. It's a recurring issue with Rust.
    #[inline]
    fn tab_size_eval(&self, column: CoordType) -> CoordType {
        // SAFETY: `set_tab_size` clamps `self.tab_size` to 1-8.
        unsafe { std::hint::assert_unchecked(self.tab_size >= 1 && self.tab_size <= 8) };
        self.tab_size - (column % self.tab_size)
    }

    /// If the cursor is at an indentation of `column`, this returns
    /// the column to which a backspace key press would delete to.
    #[inline]
    fn tab_size_prev_column(&self, column: CoordType) -> CoordType {
        // SAFETY: `set_tab_size` clamps `self.tab_size` to 1-8.
        unsafe { std::hint::assert_unchecked(self.tab_size >= 1 && self.tab_size <= 8) };
        (column - 1).max(0) / self.tab_size * self.tab_size
    }

    /// Returns whether tabs are used for indentation.
    pub fn indent_with_tabs(&self) -> bool {
        self.indent_with_tabs
    }

    /// Sets whether tabs or spaces are used for indentation.
    pub fn set_indent_with_tabs(&mut self, indent_with_tabs: bool) {
        self.indent_with_tabs = indent_with_tabs;
    }

    /// Sets whether the line the cursor is on should be highlighted.
    pub fn set_line_highlight_enabled(&mut self, enabled: bool) {
        self.line_highlight_enabled = enabled;
    }

    pub fn language(&self) -> Option<&'static Language> {
        self.language
    }

    pub fn set_language(&mut self, language: Option<&'static Language>) {
        self.language = language;
        self.highlighter_cache.invalidate_from(0);
    }

    /// Sets a ruler column, e.g. 80.
    pub fn set_ruler(&mut self, column: CoordType) {
        self.ruler = column;
    }

    pub fn reflow(&mut self) {
        self.reflow_internal(true);
    }

    fn recalc_after_content_changed(&mut self) {
        self.reflow_internal(false);
    }

    fn reflow_internal(&mut self, force: bool) {
        if force {
            self.warning_cache.borrow_mut().lines.clear();
        }
        let word_wrap_column_before = self.word_wrap_column;

        {
            // +1 onto logical_lines, because line numbers are 1-based.
            // +1 onto log10, because we want the digit width and not the actual log10.
            // +3 onto log10, because we append " | " to the line numbers to form the margin.
            self.margin_width = if self.margin_enabled {
                self.stats.logical_lines.ilog10() as CoordType + 4
            } else {
                0
            };

            let text_width = self.text_width();
            // 2 columns are required, because otherwise wide glyphs wouldn't ever fit.
            self.word_wrap_column = if let Some(edit) = &self.format_edit {
                edit.wrap_column
            } else if self.word_wrap_enabled && text_width >= 2 {
                self.wrap_chars.map_or(text_width, |count| (count * 2).min(text_width))
            } else {
                0
            };
        }

        self.cursor_for_rendering = None;

        if force || self.word_wrap_column != word_wrap_column_before {
            // Recalculate the cursor position.
            self.cursor = self.cursor_move_to_logical_internal(
                if self.word_wrap_column > 0 {
                    Default::default()
                } else {
                    self.goto_line_start(self.cursor, self.cursor.logical_pos.y)
                },
                self.cursor.logical_pos,
            );

            // Recalculate the line statistics.
            if self.word_wrap_column > 0 {
                let end = self.cursor_move_to_logical_internal(self.cursor, Point::MAX);
                self.stats.visual_lines = end.visual_pos.y + 1;
            } else {
                self.stats.visual_lines = self.stats.logical_lines;
            }
        }
    }

    /// Replaces the entire buffer contents with the given `text`.
    /// Assumes that the line count doesn't change.
    pub fn copy_from_str(&mut self, text: &dyn ReadableDocument) {
        if self.buffer.copy_from(text) {
            self.recalc_after_content_swap();
            self.cursor_move_to_logical(Point { x: CoordType::MAX, y: 0 });

            let delete = self.buffer.len() - self.cursor.offset;
            if delete != 0 {
                self.buffer.allocate_gap(self.cursor.offset, 0, delete);
            }
        }
    }

    fn recalc_after_content_swap(&mut self) {
        // If the buffer was changed, nothing we previously saved can be relied upon.
        self.undo_stack.clear();
        self.redo_stack.clear();
        self.last_history_type = HistoryType::Other;
        self.cursor = Default::default();
        self.set_selection(None);
        self.mark_as_clean();
        self.reflow();
        self.highlighter_cache.invalidate_from(0);
    }

    /// Copies the contents of the buffer into a string.
    pub fn save_as_string(&mut self, dst: &mut dyn WriteableDocument) {
        self.buffer.copy_into(dst);
        self.mark_as_clean();
    }

    /// Reads a file from disk into the text buffer, detecting encoding and BOM.
    pub fn read_file(&mut self, file: &mut File, encoding: Option<&'static str>) -> IoResult<()> {
        let scratch = scratch_arena(None);
        let buf = scratch.alloc_uninit_array();
        let mut first_chunk_len = 0;
        let mut read = 0;

        // Read enough bytes to detect the BOM.
        while first_chunk_len < BOM_MAX_LEN {
            read = file_read_uninit(file, &mut buf[first_chunk_len..])?;
            if read == 0 {
                break;
            }
            first_chunk_len += read;
        }

        if let Some(encoding) = encoding {
            self.encoding = encoding;
        } else {
            let bom = detect_bom(unsafe { buf[..first_chunk_len].assume_init_ref() });
            self.encoding = bom.unwrap_or("UTF-8");
        }

        // TODO: Since reading the file can fail, we should ensure that we also reset the cursor here.
        // I don't do it, so that `recalc_after_content_swap()` works.
        self.buffer.clear();

        let done = read == 0;
        if self.encoding == "UTF-8" {
            self.read_file_as_utf8(file, buf, first_chunk_len, done)?;
        } else {
            self.read_file_with_icu(file, buf, first_chunk_len, done)?;
        }

        // Figure out
        // * the logical line count
        // * the newline type (LF or CRLF)
        // * the indentation type (tabs or spaces)
        // * whether there's a final newline
        {
            let chunk = self.read_forward(0);
            let mut offset = 0;
            let mut lines = 0;
            // Number of lines ending in CRLF.
            let mut crlf_count = 0;
            // Number of lines starting with a tab.
            let mut tab_indentations = 0;
            // Number of lines starting with a space.
            let mut space_indentations = 0;
            // Histogram of the indentation depth of lines starting with between 2 and 8 spaces.
            // In other words, `space_indentation_sizes[0]` is the number of lines starting with 2 spaces.
            let mut space_indentation_sizes = [0; 7];

            loop {
                // Check if the line starts with a tab.
                if offset < chunk.len() && chunk[offset] == b'\t' {
                    tab_indentations += 1;
                } else {
                    // Otherwise, check how many spaces the line starts with. Searching for >8 spaces
                    // allows us to reject lines that have more than 1 level of indentation.
                    let space_indentation =
                        chunk[offset..].iter().take(9).take_while(|&&c| c == b' ').count();

                    // We'll also reject lines starting with 1 space, because that's too fickle as a heuristic.
                    if (2..=8).contains(&space_indentation) {
                        space_indentations += 1;

                        // If we encounter an indentation depth of 6, it may either be a 6-space indentation,
                        // two 3-space indentation or 3 2-space indentations. To make this work, we increment
                        // all 3 possible histogram slots.
                        //   2 -> 2
                        //   3 -> 3
                        //   4 -> 4 2
                        //   5 -> 5
                        //   6 -> 6 3 2
                        //   7 -> 7
                        //   8 -> 8 4 2
                        space_indentation_sizes[space_indentation - 2] += 1;
                        if space_indentation & 4 != 0 {
                            space_indentation_sizes[0] += 1;
                        }
                        if space_indentation == 6 || space_indentation == 8 {
                            space_indentation_sizes[space_indentation / 2 - 2] += 1;
                        }
                    }
                }

                (offset, lines) = simd::lines_fwd(chunk, offset, lines, lines + 1);

                // Check if the preceding line ended in CRLF.
                if offset >= 2 && &chunk[offset - 2..offset] == b"\r\n" {
                    crlf_count += 1;
                }

                // We'll limit our heuristics to the first 1000 lines.
                // That should hopefully be enough in practice.
                if offset >= chunk.len() || lines >= 1000 {
                    break;
                }
            }

            // We'll assume CRLF if more than half of the lines end in CRLF. If there is only a single line, we'll use the platform default.
            let newlines_are_crlf = if lines == 0 { cfg!(windows) } else { crlf_count > lines / 2 };

            // We'll assume tabs if there are more lines starting with tabs than with spaces.
            let indent_with_tabs = tab_indentations > space_indentations;
            let tab_size = if indent_with_tabs {
                // Tabs will get a visual size of 4 spaces by default.
                4
            } else {
                // Otherwise, we'll assume the most common indentation depth.
                // If there are conflicting indentation depths, we'll prefer the maximum, because in the loop
                // above we incremented the histogram slot for 2-spaces when encountering 4-spaces and so on.
                let mut max = 1;
                let mut tab_size = 4;
                for (i, &count) in space_indentation_sizes.iter().enumerate() {
                    if count >= max {
                        max = count;
                        tab_size = i as CoordType + 2;
                    }
                }
                tab_size
            };

            // If the file has more than 1000 lines, figure out how many are remaining.
            if offset < chunk.len() {
                (_, lines) = simd::lines_fwd(chunk, offset, lines, CoordType::MAX);
            }

            let final_newline = chunk.ends_with(b"\n");

            // Add 1, because the last line doesn't end in a newline (it ends in the literal end).
            self.stats.logical_lines = lines + 1;
            self.stats.visual_lines = self.stats.logical_lines;
            self.newlines_are_crlf = newlines_are_crlf;
            self.insert_final_newline = final_newline;
            self.indent_with_tabs = indent_with_tabs;
            self.tab_size = tab_size;
        }

        self.recalc_after_content_swap();
        Ok(())
    }

    fn read_file_as_utf8(
        &mut self,
        file: &mut File,
        buf: &mut [MaybeUninit<u8>; 4 * KIBI],
        first_chunk_len: usize,
        done: bool,
    ) -> io::Result<()> {
        {
            let mut first_chunk = unsafe { buf[..first_chunk_len].assume_init_ref() };
            if first_chunk.starts_with(b"\xEF\xBB\xBF") {
                first_chunk = &first_chunk[3..];
                self.encoding = "UTF-8 BOM";
            }

            self.buffer.replace(0..0, first_chunk);
        }

        if done {
            return Ok(());
        }

        // If we don't have file metadata, the input may be a pipe or a socket.
        // Every read will have the same size until we hit the end.
        let mut chunk_size = 128 * KIBI;
        let mut extra_chunk_size = 128 * KIBI;

        if let Ok(m) = file.metadata() {
            // Usually the next read of size `chunk_size` will read the entire file,
            // but if the size has changed for some reason, then `extra_chunk_size`
            // should be large enough to read the rest of the file.
            // 4KiB is not too large and not too slow.
            let len = m.len() as usize;
            chunk_size = len.saturating_sub(first_chunk_len);
            extra_chunk_size = 4 * KIBI;
        }

        loop {
            let gap = self.buffer.allocate_gap(self.text_length(), chunk_size, 0);
            if gap.is_empty() {
                break;
            }

            let read = file.read(gap)?;
            if read == 0 {
                break;
            }

            self.buffer.commit_gap(read);
            chunk_size = extra_chunk_size;
        }

        Ok(())
    }

    fn read_file_with_icu(
        &mut self,
        file: &mut File,
        buf: &mut [MaybeUninit<u8>; 4 * KIBI],
        first_chunk_len: usize,
        mut done: bool,
    ) -> IoResult<()> {
        let scratch = scratch_arena(None);
        let pivot_buffer = scratch.alloc_uninit_slice(4 * KIBI);
        let mut c = icu::Converter::new(pivot_buffer, self.encoding, "UTF-8")?;
        let mut first_chunk = unsafe { buf[..first_chunk_len].assume_init_ref() };

        while !first_chunk.is_empty() {
            let off = self.text_length();
            let gap = self.buffer.allocate_gap(off, 8 * KIBI, 0);
            let (input_advance, mut output_advance) =
                c.convert(first_chunk, slice_as_uninit_mut(gap))?;

            // Remove the BOM from the file, if this is the first chunk.
            // Our caller ensures to only call us once the BOM has been identified,
            // which means that if there's a BOM it must be wholly contained in this chunk.
            if off == 0 {
                let written = &mut gap[..output_advance];
                if written.starts_with(b"\xEF\xBB\xBF") {
                    written.copy_within(3.., 0);
                    output_advance -= 3;
                }
            }

            self.buffer.commit_gap(output_advance);
            first_chunk = &first_chunk[input_advance..];
        }

        let mut buf_len = 0;

        loop {
            if !done {
                let read = file_read_uninit(file, &mut buf[buf_len..])?;
                buf_len += read;
                done = read == 0;
            }

            let gap = self.buffer.allocate_gap(self.text_length(), 8 * KIBI, 0);
            if gap.is_empty() {
                break;
            }

            let read = unsafe { buf[..buf_len].assume_init_ref() };
            let (input_advance, output_advance) = c.convert(read, slice_as_uninit_mut(gap))?;

            self.buffer.commit_gap(output_advance);

            let flush = done && buf_len == 0;
            buf_len -= input_advance;
            buf.copy_within(input_advance.., 0);

            if flush {
                break;
            }
        }

        Ok(())
    }

    /// Writes the text buffer contents to a file, handling BOM and encoding.
    pub fn write_file(&mut self, file: &mut File) -> IoResult<()> {
        let mut offset = 0;

        if self.encoding.starts_with("UTF-8") {
            if self.encoding == "UTF-8 BOM" {
                file.write_all(b"\xEF\xBB\xBF")?;
            }
            loop {
                let chunk = self.read_forward(offset);
                if chunk.is_empty() {
                    break;
                }
                file.write_all(chunk)?;
                offset += chunk.len();
            }
        } else {
            self.write_file_with_icu(file)?;
        }

        self.mark_as_clean();
        Ok(())
    }

    fn write_file_with_icu(&mut self, file: &mut File) -> IoResult<()> {
        let scratch = scratch_arena(None);
        let pivot_buffer = scratch.alloc_uninit_slice(4 * KIBI);
        let buf = scratch.alloc_uninit_slice(4 * KIBI);
        let mut c = icu::Converter::new(pivot_buffer, "UTF-8", self.encoding)?;
        let mut offset = 0;

        // Write the BOM for the encodings we know need it.
        if self.encoding.starts_with("UTF-16")
            || self.encoding.starts_with("UTF-32")
            || self.encoding == "GB18030"
        {
            let (_, output_advance) = c.convert(b"\xEF\xBB\xBF", buf)?;
            let chunk = unsafe { buf[..output_advance].assume_init_ref() };
            file.write_all(chunk)?;
        }

        loop {
            let chunk = self.read_forward(offset);
            let (input_advance, output_advance) = c.convert(chunk, buf)?;
            let chunk = unsafe { buf[..output_advance].assume_init_ref() };

            file.write_all(chunk)?;
            offset += input_advance;

            if chunk.is_empty() {
                break;
            }
        }

        Ok(())
    }

    /// Returns the current selection.
    pub fn has_selection(&self) -> bool {
        self.selection.is_some()
    }

    pub fn is_selection_latched(&self) -> bool {
        self.selection_latch.is_some()
    }

    pub fn start_selection_latch(&mut self) {
        if self.selection_latch.is_none() {
            self.clear_selection();
            self.selection_latch = Some(self.cursor.logical_pos);
        }
    }

    pub fn finish_selection_latch(&mut self) {
        self.selection_latch = None;
    }

    /// Normalize textarea keys while keeping Enter/Escape from editing the text.
    pub(crate) fn selection_latch_key(
        &mut self,
        input: crate::input::InputKey,
    ) -> Option<crate::input::InputKey> {
        use crate::input::{kbmod, vk};
        let key = input.key();
        let arrow = matches!(key, vk::LEFT | vk::RIGHT | vk::UP | vk::DOWN);
        let modifiers = input.modifiers();
        if arrow && modifiers.contains(kbmod::CTRL) && modifiers.contains(kbmod::SHIFT) {
            self.start_selection_latch();
        }
        if self.is_selection_latched() {
            if arrow || matches!(key, vk::HOME | vk::END | vk::PRIOR | vk::NEXT) {
                return Some(kbmod::SHIFT | key);
            }
            if key == vk::RETURN {
                self.finish_selection_latch();
                return None;
            }
            if key == vk::ESCAPE {
                self.clear_selection();
                return None;
            }
        }
        Some(input)
    }

    fn set_selection(&mut self, selection: Option<TextBufferSelection>) -> u32 {
        let selection = selection.map(|s| {
            if !self.is_format_editing() {
                return s;
            }
            let beg = self
                .constrain_format_cursor(self.cursor_move_to_logical_internal(self.cursor, s.beg));
            let end = self
                .constrain_format_cursor(self.cursor_move_to_logical_internal(self.cursor, s.end));
            TextBufferSelection { beg: beg.logical_pos, end: end.logical_pos }
        });
        self.selection = selection.filter(|s| s.beg != s.end);
        self.selection_generation = self.selection_generation.wrapping_add(1);
        self.selection_generation
    }

    /// Moves the cursor by `offset` and updates the selection to contain it.
    pub fn selection_update_offset(&mut self, offset: usize) {
        self.set_cursor_for_selection(self.cursor_move_to_offset_internal(self.cursor, offset));
    }

    /// Moves the cursor to `visual_pos` and updates the selection to contain it.
    pub fn selection_update_visual(&mut self, visual_pos: Point) {
        self.set_cursor_for_selection(self.cursor_move_to_visual_internal(self.cursor, visual_pos));
    }

    /// Moves the cursor to `logical_pos` and updates the selection to contain it.
    pub fn selection_update_logical(&mut self, logical_pos: Point) {
        self.set_cursor_for_selection(
            self.cursor_move_to_logical_internal(self.cursor, logical_pos),
        );
    }

    /// Moves the cursor by `delta` and updates the selection to contain it.
    pub fn selection_update_delta(&mut self, granularity: CursorMovement, delta: CoordType) {
        self.set_cursor_for_selection(self.cursor_move_delta_internal(
            self.cursor,
            granularity,
            delta,
        ));
    }

    /// Select the current word.
    pub fn select_word(&mut self) {
        let Range { start, end } = navigation::word_select(&self.buffer, self.cursor.offset);
        let beg = self.cursor_move_to_offset_internal(self.cursor, start);
        let end = self.cursor_move_to_offset_internal(beg, end);
        unsafe { self.set_cursor(end) };
        self.set_selection(Some(TextBufferSelection {
            beg: beg.logical_pos,
            end: end.logical_pos,
        }));
    }

    /// Select the current line.
    pub fn select_line(&mut self) {
        let beg = self.cursor_move_to_logical_internal(
            self.cursor,
            Point { x: 0, y: self.cursor.logical_pos.y },
        );
        let end = self
            .cursor_move_to_logical_internal(beg, Point { x: 0, y: self.cursor.logical_pos.y + 1 });
        unsafe { self.set_cursor(end) };
        self.set_selection(Some(TextBufferSelection {
            beg: beg.logical_pos,
            end: end.logical_pos,
        }));
    }

    /// Select the entire document.
    pub fn select_all(&mut self) {
        let beg = Default::default();
        let end = self.cursor_move_to_logical_internal(beg, Point::MAX);
        unsafe { self.set_cursor(end) };
        self.set_selection(Some(TextBufferSelection {
            beg: beg.logical_pos,
            end: end.logical_pos,
        }));
    }

    /// Starts a new selection, if there's none already.
    pub fn start_selection(&mut self) {
        if self.selection.is_none() {
            self.set_selection(Some(TextBufferSelection {
                beg: self.cursor.logical_pos,
                end: self.cursor.logical_pos,
            }));
        }
    }

    /// Destroy the current selection.
    pub fn clear_selection(&mut self) -> bool {
        self.finish_selection_latch();
        let had_selection = self.selection.is_some();
        self.set_selection(None);
        had_selection
    }

    /// Find the next occurrence of the given `pattern` and select it.
    pub fn find_and_select(&mut self, pattern: &str, options: SearchOptions) -> icu::Result<()> {
        if let Some(search) = &mut self.search {
            let search = search.get_mut();
            // When the search input changes we must reset the search.
            if search.pattern != pattern || search.options != options {
                self.search = None;
            }

            // When transitioning from some search to no search, we must clear the selection.
            if pattern.is_empty()
                && let Some(TextBufferSelection { beg, .. }) = self.selection
            {
                self.cursor_move_to_logical(beg);
            }
        }

        if pattern.is_empty() {
            return Ok(());
        }

        let search = match &self.search {
            Some(search) => unsafe { &mut *search.get() },
            None => {
                let search = self.find_construct_search(pattern, options)?;
                self.search = Some(UnsafeCell::new(search));
                unsafe { &mut *self.search.as_ref().unwrap().get() }
            }
        };

        // If we previously searched through the entire document and found 0 matches,
        // then we can avoid searching again.
        if search.no_matches {
            return Ok(());
        }

        // If the user moved the cursor since the last search, but the needle remained the same,
        // we still need to move the start of the search to the new cursor position.
        let next_search_offset = if self.selection_generation == search.selection_generation {
            search.next_search_offset
        } else {
            match self.selection {
                Some(TextBufferSelection { beg, end }) => {
                    self.cursor_move_to_logical_internal(self.cursor, beg.min(end)).offset
                }
                _ => self.cursor.offset,
            }
        };

        self.find_select_next(search, next_search_offset, true);
        Ok(())
    }

    /// Find the next occurrence of the given `pattern` and replace it with `replacement`.
    pub fn find_and_replace(
        &mut self,
        pattern: &str,
        options: SearchOptions,
        replacement: &[u8],
    ) -> icu::Result<()> {
        // Editors traditionally replace the previous search hit, not the next possible one.
        if let Some(search) = &self.search {
            let search = unsafe { &mut *search.get() };
            if search.selection_generation == self.selection_generation {
                let scratch = scratch_arena(None);
                let zero_width = self.selection.is_none();
                let parsed_replacements =
                    Self::find_parse_replacement(&scratch, &mut *search, replacement);
                let replacement =
                    self.find_fill_replacement(&mut *search, replacement, &parsed_replacements);
                if self.is_format_editing()
                    && replacement.iter().any(|byte| matches!(byte, b'\r' | b'\n'))
                {
                    return Err(icu::ILLEGAL_ARGUMENT_ERROR);
                }
                self.write_raw(&replacement);

                // After replacing a zero-width match, advance past it so that find_and_select wraps to the
                // next match rather than finding the same anchor (e.g. `$`) again at the same line end.
                if zero_width {
                    search.next_search_offset =
                        self.find_advance_past_zero_width(self.active_edit_off).unwrap_or(0);
                }
            }
        }

        self.find_and_select(pattern, options)
    }

    /// Find all occurrences of the given `pattern` and replace them with `replacement`.
    pub fn find_and_replace_all(
        &mut self,
        pattern: &str,
        options: SearchOptions,
        replacement: &[u8],
    ) -> icu::Result<()> {
        self.edit_begin_grouping();

        let scratch = scratch_arena(None);
        let mut search = self.find_construct_search(pattern, options)?;
        let mut offset = 0;
        let parsed_replacements = Self::find_parse_replacement(&scratch, &mut search, replacement);

        while let Some(range) = self.find_select_next(&mut search, offset, false) {
            let replacement =
                self.find_fill_replacement(&mut search, replacement, &parsed_replacements);
            if self.is_format_editing()
                && replacement.iter().any(|byte| matches!(byte, b'\r' | b'\n'))
            {
                self.edit_end_grouping();
                return Err(icu::ILLEGAL_ARGUMENT_ERROR);
            }
            self.write_raw(&replacement);

            // The `active_edit_off` points to the end of the last edit made by `write_raw()`.
            // This differs from the self.cursor.offset, if `write_raw()` did an `insert_final_newline`.
            offset = self.active_edit_off;

            // Avoid infinite loops when hitting zero-length matches
            // by advancing past the zero-length match location.
            //
            // This is technically not entirely correct. For instance imagine replacing
            // "^|f" with "x" in "foo". It should technically produce "xxoo", but I
            // found that other editors also do it wrong, so it can't matter too much.
            if range.is_empty() {
                offset = match self.find_advance_past_zero_width(offset) {
                    Some(next) => next,
                    None => break,
                };
            }
        }

        self.edit_end_grouping();
        Ok(())
    }

    /// After replacing a zero-width match, compute the offset to resume
    /// searching from. Returns `None` if we're at the end of the buffer.
    fn find_advance_past_zero_width(&self, offset: usize) -> Option<usize> {
        let cursor = self.cursor_move_to_offset_internal(self.cursor, offset);
        let next = self.cursor_move_delta_internal(cursor, CursorMovement::Grapheme, 1);
        (next.offset > offset).then_some(next.offset)
    }

    fn find_construct_search(
        &self,
        pattern: &str,
        options: SearchOptions,
    ) -> icu::Result<ActiveSearch> {
        if pattern.is_empty() {
            return Err(icu::ILLEGAL_ARGUMENT_ERROR);
        }

        let sanitized_pattern = if options.whole_word && options.use_regex {
            Cow::Owned(format!(r"\b(?:{pattern})\b"))
        } else if options.whole_word {
            let mut p = String::with_capacity(pattern.len() + 16);
            p.push_str(r"\b");

            // Escape regex special characters.
            let b = unsafe { p.as_mut_vec() };
            for &byte in pattern.as_bytes() {
                match byte {
                    b'*' | b'?' | b'+' | b'[' | b'(' | b')' | b'{' | b'}' | b'^' | b'$' | b'|'
                    | b'\\' | b'.' => {
                        b.push(b'\\');
                        b.push(byte);
                    }
                    _ => b.push(byte),
                }
            }

            p.push_str(r"\b");
            Cow::Owned(p)
        } else {
            Cow::Borrowed(pattern)
        };

        let mut flags = icu::Regex::MULTILINE;
        if !options.match_case {
            flags |= icu::Regex::CASE_INSENSITIVE;
        }
        if !options.use_regex && !options.whole_word {
            flags |= icu::Regex::LITERAL;
        }

        // Move the start of the search to the start of the selection,
        // or otherwise to the current cursor position.

        let text = unsafe { icu::Text::new(self)? };
        let regex = unsafe { icu::Regex::new(&sanitized_pattern, flags, &text)? };

        Ok(ActiveSearch {
            pattern: pattern.to_string(),
            options,
            text,
            regex,
            buffer_generation: self.buffer.generation(),
            selection_generation: 0,
            next_search_offset: 0,
            no_matches: false,
        })
    }

    fn find_select_next(
        &mut self,
        search: &mut ActiveSearch,
        offset: usize,
        wrap: bool,
    ) -> Option<Range<usize>> {
        if search.buffer_generation != self.buffer.generation() {
            unsafe { search.regex.set_text(&mut search.text, offset) };
            search.buffer_generation = self.buffer.generation();
            search.next_search_offset = offset;
        } else if search.next_search_offset != offset {
            search.next_search_offset = offset;
            search.regex.reset(offset);
        }

        let mut hit = search.regex.next();
        if let Some(edit) = &self.format_edit {
            while hit
                .as_ref()
                .is_some_and(|range| range.start < edit.source.start || range.end > edit.source.end)
            {
                hit = search.regex.next();
            }
        }

        // If we hit the end of the buffer, and we know that there's something to find,
        // start the search again from the beginning (= wrap around).
        if wrap && hit.is_none() && search.next_search_offset != 0 {
            search.next_search_offset = 0;
            search.regex.reset(0);
            hit = search.regex.next();
            if let Some(edit) = &self.format_edit {
                while hit.as_ref().is_some_and(|range| {
                    range.start < edit.source.start || range.end > edit.source.end
                }) {
                    hit = search.regex.next();
                }
            }
        }

        search.selection_generation = if let Some(range) = &hit {
            // Now the search offset is no more at the start of the buffer.
            search.next_search_offset = range.end;

            let beg = self.cursor_move_to_offset_internal(self.cursor, range.start);
            let end = self.cursor_move_to_offset_internal(beg, range.end);

            unsafe { self.set_cursor(end) };
            self.make_cursor_visible();

            self.set_selection(Some(TextBufferSelection {
                beg: beg.logical_pos,
                end: end.logical_pos,
            }))
        } else {
            // Avoid searching through the entire document again if we know there's nothing to find.
            search.no_matches = true;
            self.set_selection(None)
        };

        hit
    }

    fn find_parse_replacement<'a>(
        arena: &'a Arena,
        search: &mut ActiveSearch,
        replacement: &[u8],
    ) -> BVec<'a, RegexReplacement<'a>> {
        let mut res = BVec::empty();

        if !search.options.use_regex {
            return res;
        }

        let group_count = search.regex.group_count();
        let mut text = BVec::empty();
        let mut text_beg = 0;

        loop {
            let mut off = memchr2(b'$', b'\\', replacement, text_beg);

            // Push the raw, unescaped text, if any.
            if text_beg < off {
                text.extend_from_slice(arena, &replacement[text_beg..off]);
            }

            // Unescape any escaped characters.
            while off < replacement.len() && replacement[off] == b'\\' {
                off += 2;

                // If this backslash is the last character (e.g. because
                // `replacement` is just 1 byte long, holding just b"\\"),
                // we can't unescape it. In that case, we map it to `b'\\'` here.
                // This results in us appending a literal backslash to the text.
                let ch = replacement.get(off - 1).map_or(b'\\', |&c| c);

                // Unescape and append the character.
                text.push(
                    arena,
                    match ch {
                        b'n' => b'\n',
                        b'r' => b'\r',
                        b't' => b'\t',
                        ch => ch,
                    },
                );
            }

            // Parse out a group number, if any.
            let mut group = -1;
            if off < replacement.len() && replacement[off] == b'$' {
                let mut beg = off;
                let mut end = off + 1;
                let mut acc = 0i32;
                let mut acc_bad = true;

                if end < replacement.len() {
                    let ch = replacement[end];

                    if ch == b'$' {
                        // Translate "$$" to "$".
                        beg += 1;
                        end += 1;
                    } else if ch.is_ascii_digit() {
                        // Parse "$1234" into 1234i32.
                        // If the number is larger than the group count,
                        // we flag `acc_bad` which causes us to treat it as text.
                        acc_bad = false;
                        while {
                            acc =
                                acc.wrapping_mul(10).wrapping_add((replacement[end] - b'0') as i32);
                            acc_bad |= acc > group_count;
                            end += 1;
                            end < replacement.len() && replacement[end].is_ascii_digit()
                        } {}
                    }
                }

                if !acc_bad {
                    group = acc;
                } else {
                    text.extend_from_slice(arena, &replacement[beg..end]);
                }

                off = end;
            }

            if !text.is_empty() {
                res.push(arena, RegexReplacement::Text(text));
                text = BVec::empty();
            }
            if group >= 0 {
                res.push(arena, RegexReplacement::Group(group));
            }

            text_beg = off;
            if text_beg >= replacement.len() {
                break;
            }
        }

        res
    }

    fn find_fill_replacement<'a>(
        &self,
        search: &mut ActiveSearch,
        replacement: &'a [u8],
        parsed_replacements: &[RegexReplacement],
    ) -> Cow<'a, [u8]> {
        if !search.options.use_regex {
            Cow::Borrowed(replacement)
        } else {
            let mut res = Vec::new();

            for replacement in parsed_replacements {
                match replacement {
                    RegexReplacement::Text(text) => res.extend_from_slice(text),
                    RegexReplacement::Group(group) => {
                        if let Some(range) = search.regex.group(*group) {
                            self.buffer.extract_raw(range, &mut res, usize::MAX);
                        }
                    }
                }
            }

            Cow::Owned(res)
        }
    }

    fn measurement_config(&self) -> MeasurementConfig<'_> {
        self.ruby_cache.prepare(self.buffer.generation());
        let config = MeasurementConfig::new(&self.buffer)
            .with_word_wrap_column(self.word_wrap_column)
            .with_wrap_at_any_cluster(self.wrap_chars.is_some())
            .with_tab_size(self.tab_size)
            .with_hidden_text(if self.ruby_display { Some(&self.ruby_cache) } else { None });
        match &self.format_edit {
            Some(edit) => config.with_source_line(&edit.source, &edit.wraps),
            None => config,
        }
    }

    fn goto_line_start(&self, cursor: Cursor, y: CoordType) -> Cursor {
        let mut result = cursor;
        let mut seek_to_line_start = true;

        if y > result.logical_pos.y {
            while y > result.logical_pos.y {
                let chunk = self.read_forward(result.offset);
                if chunk.is_empty() {
                    break;
                }

                let (delta, line) = simd::lines_fwd(chunk, 0, result.logical_pos.y, y);
                result.offset += delta;
                result.logical_pos.y = line;
            }

            // If we're at the end of the buffer, we could either be there because the last
            // character in the buffer is genuinely a newline, or because the buffer ends in a
            // line of text without trailing newline. The only way to make sure is to seek
            // backwards to the line start again. But otherwise we can skip that.
            seek_to_line_start =
                result.offset == self.text_length() && result.offset != cursor.offset;
        }

        if seek_to_line_start {
            loop {
                let chunk = self.read_backward(result.offset);
                if chunk.is_empty() {
                    break;
                }

                let (delta, line) = simd::lines_bwd(chunk, chunk.len(), result.logical_pos.y, y);
                result.offset -= chunk.len() - delta;
                result.logical_pos.y = line;
                if delta > 0 {
                    break;
                }
            }
        }

        if result.offset == cursor.offset {
            return result;
        }

        result.logical_pos.x = 0;
        result.visual_pos.x = 0;
        result.visual_pos.y = result.logical_pos.y;
        result.column = 0;
        result.wrap_opp = false;

        if self.word_wrap_column > 0 {
            let upward = result.offset < cursor.offset;
            let (top, bottom) = if upward { (result, cursor) } else { (cursor, result) };

            let mut bottom_remeasured =
                self.measurement_config().with_cursor(top).goto_logical(bottom.logical_pos);

            // The second problem is that visual positions can be ambiguous. A single logical position
            // can map to two visual positions: One at the end of the preceding line in front of
            // a word wrap, and another at the start of the next line after the same word wrap.
            //
            // This, however, only applies if we go upwards, because only then `bottom ≅ cursor`,
            // and thus only then this `bottom` is ambiguous. Otherwise, `bottom ≅ result`
            // and `result` is at a line start which is never ambiguous.
            if upward {
                let a = bottom_remeasured.visual_pos.x;
                let b = bottom.visual_pos.x;
                bottom_remeasured.visual_pos.y = bottom_remeasured.visual_pos.y
                    + (a != 0 && b == 0) as CoordType
                    - (a == 0 && b != 0) as CoordType;
            }

            let mut delta = bottom_remeasured.visual_pos.y - top.visual_pos.y;
            if upward {
                delta = -delta;
            }

            result.visual_pos.y = cursor.visual_pos.y + delta;
        }

        result
    }

    fn cursor_move_to_offset_internal(&self, mut cursor: Cursor, offset: usize) -> Cursor {
        if offset == cursor.offset {
            return cursor;
        }

        // goto_line_start() is fast for seeking across lines _if_ line wrapping is disabled.
        // For backward seeking we have to use it either way, so we're covered there.
        // This implements the forward seeking portion, if it's approx. worth doing so.
        if self.word_wrap_column <= 0 && offset.saturating_sub(cursor.offset) > 1024 {
            // Replacing this with a more optimal, direct memchr() loop appears
            // to improve performance only marginally by another 2% or so.
            // Still, it's kind of "meh" looking at how poorly this is implemented...
            loop {
                let next = self.goto_line_start(cursor, cursor.logical_pos.y + 1);
                // Stop when we either ran past the target offset,
                // or when we hit the end of the buffer and `goto_line_start` backtracked to the line start.
                if next.offset > offset || next.offset <= cursor.offset {
                    break;
                }
                cursor = next;
            }
        }

        while offset < cursor.offset {
            cursor = self.goto_line_start(cursor, cursor.logical_pos.y - 1);
        }

        self.measurement_config().with_cursor(cursor).goto_offset(offset)
    }

    fn cursor_move_to_logical_internal(&self, mut cursor: Cursor, pos: Point) -> Cursor {
        let pos = Point { x: pos.x.max(0), y: pos.y.max(0) };

        if pos == cursor.logical_pos {
            return cursor;
        }

        // goto_line_start() is the fastest way for seeking across lines. As such we always
        // use it if the requested `.y` position is different. We still need to use it if the
        // `.x` position is smaller, but only because `goto_logical()` cannot seek backwards.
        if pos.y != cursor.logical_pos.y || pos.x < cursor.logical_pos.x {
            cursor = self.goto_line_start(cursor, pos.y);
        }

        self.measurement_config().with_cursor(cursor).goto_logical(pos)
    }

    fn cursor_move_to_visual_internal(&self, mut cursor: Cursor, pos: Point) -> Cursor {
        let pos = Point { x: pos.x.max(0), y: pos.y.max(0) };

        if pos == cursor.visual_pos {
            return cursor;
        }

        if self.word_wrap_column <= 0 {
            // Identical to the fast-pass in `cursor_move_to_logical_internal()`.
            if pos.y != cursor.visual_pos.y || pos.x < cursor.visual_pos.x {
                cursor = self.goto_line_start(cursor, pos.y);
            }
        } else {
            // `goto_visual()` can only seek forward, so we need to seek backward here if needed.
            // NOTE that this intentionally doesn't use the `Eq` trait of `Point`, because if
            // `pos.y == cursor.visual_pos.y` we don't need to go to `cursor.logical_pos.y - 1`.
            while pos.y < cursor.visual_pos.y {
                cursor = self.goto_line_start(cursor, cursor.logical_pos.y - 1);
            }
            if pos.y == cursor.visual_pos.y && pos.x < cursor.visual_pos.x {
                cursor = self.goto_line_start(cursor, cursor.logical_pos.y);
            }
        }

        let cursor = self.measurement_config().with_cursor(cursor).goto_visual(pos);
        self.skip_hidden_ruby(cursor, 1)
    }

    fn cursor_move_delta_internal(
        &self,
        cursor: Cursor,
        granularity: CursorMovement,
        delta: CoordType,
    ) -> Cursor {
        if !self.ruby_display || delta == 0 {
            return self.cursor_move_delta_source_internal(cursor, granularity, delta);
        }
        let cursor = self.skip_hidden_ruby(cursor, 1);
        match granularity {
            CursorMovement::Word => {
                let moved = self.cursor_move_delta_source_internal(cursor, granularity, delta);
                self.skip_hidden_ruby(moved, delta.signum())
            }
            CursorMovement::Grapheme => {
                let mut cursor = cursor;
                for _ in 0..delta.unsigned_abs() {
                    let next = self.cursor_move_delta_source_internal(
                        cursor,
                        CursorMovement::Grapheme,
                        delta.signum(),
                    );
                    let next = self.skip_hidden_ruby(next, delta.signum());
                    if cursor.offset == next.offset {
                        break;
                    }
                    cursor = next;
                }
                cursor
            }
        }
    }

    fn skip_hidden_ruby(&self, mut cursor: Cursor, direction: CoordType) -> Cursor {
        while let Some(range) = self.hidden_ruby_range(cursor.offset) {
            if direction > 0 {
                cursor = self.cursor_move_to_offset_internal(cursor, range.end);
            } else {
                cursor = self.cursor_move_to_offset_internal(cursor, range.start);
                if cursor.offset == 0 {
                    break;
                }
                cursor =
                    self.cursor_move_delta_source_internal(cursor, CursorMovement::Grapheme, -1);
            }
        }
        cursor
    }

    fn cursor_move_delta_source_internal(
        &self,
        mut cursor: Cursor,
        granularity: CursorMovement,
        mut delta: CoordType,
    ) -> Cursor {
        if delta == 0 {
            return cursor;
        }

        let sign = if delta > 0 { 1 } else { -1 };

        match granularity {
            CursorMovement::Grapheme => {
                let start_x = if delta > 0 { 0 } else { CoordType::MAX };

                loop {
                    let target_x = cursor.logical_pos.x + delta;

                    cursor = self.cursor_move_to_logical_internal(
                        cursor,
                        Point { x: target_x, y: cursor.logical_pos.y },
                    );

                    // We can stop if we ran out of remaining delta
                    // (or perhaps ran past the goal; in either case the sign would've changed),
                    // or if we hit the beginning or end of the buffer.
                    delta = target_x - cursor.logical_pos.x;
                    if delta.signum() != sign
                        || (delta < 0 && cursor.offset == 0)
                        || (delta > 0 && cursor.offset >= self.text_length())
                    {
                        break;
                    }

                    cursor = self.cursor_move_to_logical_internal(
                        cursor,
                        Point { x: start_x, y: cursor.logical_pos.y + sign },
                    );

                    // We crossed a newline which counts for 1 grapheme cluster.
                    // So, we also need to run the same check again.
                    delta -= sign;
                    if delta.signum() != sign
                        || cursor.offset == 0
                        || cursor.offset >= self.text_length()
                    {
                        break;
                    }
                }
            }
            CursorMovement::Word => {
                let doc = &self.buffer as &dyn ReadableDocument;
                let mut offset = self.cursor.offset;

                while delta != 0 {
                    if delta < 0 {
                        offset = navigation::word_backward(doc, offset);
                    } else {
                        offset = navigation::word_forward(doc, offset);
                    }
                    delta -= sign;
                }

                cursor = self.cursor_move_to_offset_internal(cursor, offset);
            }
        }

        cursor
    }

    /// Moves the cursor to the given offset.
    pub fn cursor_move_to_offset(&mut self, offset: usize) {
        unsafe { self.set_cursor(self.cursor_move_to_offset_internal(self.cursor, offset)) }
    }

    /// Moves the cursor to the given logical position.
    pub fn cursor_move_to_logical(&mut self, pos: Point) {
        unsafe { self.set_cursor(self.cursor_move_to_logical_internal(self.cursor, pos)) }
    }

    /// Moves the cursor to the given visual position.
    pub fn cursor_move_to_visual(&mut self, pos: Point) {
        unsafe { self.set_cursor(self.cursor_move_to_visual_internal(self.cursor, pos)) }
    }

    /// Moves the cursor by the given delta.
    pub fn cursor_move_delta(&mut self, granularity: CursorMovement, delta: CoordType) {
        unsafe { self.set_cursor(self.cursor_move_delta_internal(self.cursor, granularity, delta)) }
    }

    /// Sets the cursor to the given position, and clears the selection.
    ///
    /// # Safety
    ///
    /// This function performs no checks that the cursor is valid. "Valid" in this case means
    /// that the TextBuffer has not been modified since you received the cursor from this class.
    pub unsafe fn set_cursor(&mut self, cursor: Cursor) {
        self.finish_selection_latch();
        self.set_cursor_internal(cursor);
        self.last_history_type = HistoryType::Other;
        self.set_selection(None);
    }

    fn set_cursor_for_selection(&mut self, cursor: Cursor) {
        let beg = self.selection_latch.unwrap_or(match self.selection {
            Some(TextBufferSelection { beg, .. }) => beg,
            None => self.cursor.logical_pos,
        });

        self.set_cursor_internal(cursor);
        self.last_history_type = HistoryType::Other;

        let end = self.cursor.logical_pos;
        self.set_selection(if beg == end { None } else { Some(TextBufferSelection { beg, end }) });
    }

    fn set_cursor_internal(&mut self, cursor: Cursor) {
        let cursor = self.constrain_format_cursor(cursor);
        debug_assert!(cursor.offset <= self.text_length());
        debug_assert!(cursor.logical_pos.x >= 0);
        debug_assert!(cursor.logical_pos.y >= 0);
        debug_assert!(cursor.logical_pos.y <= self.stats.logical_lines);
        debug_assert!(cursor.visual_pos.x >= 0);
        debug_assert!(
            self.is_format_editing()
                || self.word_wrap_column <= 0
                || cursor.visual_pos.x <= self.word_wrap_column
        );
        debug_assert!(cursor.visual_pos.y >= 0);
        debug_assert!(cursor.visual_pos.y <= self.stats.visual_lines);
        self.cursor = cursor;
    }

    /// Extracts a rectangular region of the text buffer and writes it to the framebuffer.
    /// The `destination` rect is framebuffer coordinates. The extracted region within this
    /// text buffer has the given `origin` and the same size as the `destination` rect.
    pub fn render(
        &mut self,
        origin: Point,
        destination: Rect,
        focused: bool,
        fb: &mut Framebuffer,
    ) -> Option<RenderResult> {
        if destination.is_empty() {
            return None;
        }

        let width = destination.width();
        let height = destination.height();
        let line_number_width = self.margin_width.max(3) as usize - 3;
        let text_width = width - self.margin_width;
        let mut visual_pos_x_max = 0;

        // Pick the cursor closer to the `origin.y`.
        let mut cursor = {
            let a = self.cursor;
            let b = self.cursor_for_rendering.unwrap_or_default();
            let da = (a.visual_pos.y - origin.y).abs();
            let db = (b.visual_pos.y - origin.y).abs();
            if da < db { a } else { b }
        };

        let [selection_beg, selection_end] = match self.selection {
            None => [Point::MIN, Point::MIN],
            Some(TextBufferSelection { beg, end }) => minmax(beg, end),
        };

        for y in 0..height {
            let scratch = scratch_arena(None);
            let mut line = BVec::empty();
            line.reserve(&*scratch, width as usize * 2);

            let visual_line = origin.y + y;
            let mut cursor_beg =
                self.cursor_move_to_visual_internal(cursor, Point { x: origin.x, y: visual_line });
            let cursor_end = self.cursor_move_to_visual_internal(
                cursor_beg,
                Point { x: origin.x + text_width, y: visual_line },
            );

            // Accelerate the next render pass by remembering where we started off.
            if y == 0 {
                self.cursor_for_rendering = Some(cursor_beg);
            }

            if line_number_width != 0 {
                if visual_line >= self.stats.visual_lines {
                    // Past the end of the buffer? Place "    | " in the margin.
                    // Since we know that we won't see line numbers greater than i64::MAX (9223372036854775807)
                    // any time soon, we can use a static string as the template (`MARGIN`) and slice it,
                    // because `line_number_width` can't possibly be larger than 19.
                    let off = 19 - line_number_width;
                    unsafe { std::hint::assert_unchecked(off < MARGIN_TEMPLATE.len()) };
                    line.extend_from_slice(&*scratch, &MARGIN_TEMPLATE[off..]);
                } else if self.word_wrap_column <= 0 || cursor_beg.logical_pos.x == 0 {
                    // Regular line? Place "123 | " in the margin.
                    arena_write_fmt!(
                        &*scratch,
                        line,
                        "{:1$} │ ",
                        cursor_beg.logical_pos.y + 1,
                        line_number_width
                    );
                } else {
                    // Wrapped line? Place " ... | " in the margin.
                    let number_width = (cursor_beg.logical_pos.y + 1).ilog10() as usize + 1;
                    arena_write_fmt!(
                        &*scratch,
                        line,
                        "{0:1$}{0:∙<2$} │ ",
                        "",
                        line_number_width - number_width,
                        number_width
                    );
                    // Blending in the background color will "dim" the indicator dots.
                    let left = destination.left;
                    let top = destination.top + y;
                    fb.blend_fg(
                        Rect {
                            left,
                            top,
                            right: left + line_number_width as CoordType,
                            bottom: top + 1,
                        },
                        fb.indexed_alpha(IndexedColor::Background, 1, 2),
                    );
                }
            }

            let mut selection_off = 0..0;

            // Figure out the selection range on this line, if any.
            if cursor_beg.visual_pos.y == visual_line
                && selection_beg <= cursor_end.logical_pos
                && selection_end >= cursor_beg.logical_pos
            {
                let mut cursor = cursor_beg;

                // By default, we assume the entire line is selected.
                let mut selection_pos_beg = 0;
                let mut selection_pos_end = COORD_TYPE_SAFE_MAX;
                selection_off.start = cursor_beg.offset;
                selection_off.end = cursor_end.offset;

                // The start of the selection is within this line. We need to update selection_beg.
                if selection_beg <= cursor_end.logical_pos
                    && selection_beg >= cursor_beg.logical_pos
                {
                    cursor = self.cursor_move_to_logical_internal(cursor, selection_beg);
                    selection_off.start = cursor.offset;
                    selection_pos_beg = cursor.visual_pos.x;
                }

                // The end of the selection is within this line. We need to update selection_end.
                if selection_end <= cursor_end.logical_pos
                    && selection_end >= cursor_beg.logical_pos
                {
                    cursor = self.cursor_move_to_logical_internal(cursor, selection_end);
                    selection_off.end = cursor.offset;
                    selection_pos_end = cursor.visual_pos.x;
                }

                let left = destination.left + self.margin_width - origin.x;
                let top = destination.top + y;
                let rect = Rect {
                    left: left + selection_pos_beg.max(origin.x),
                    top,
                    right: left + selection_pos_end.min(origin.x + text_width),
                    bottom: top + 1,
                };

                let mut bg = fb.indexed(IndexedColor::Foreground).oklab_blend(fb.indexed_alpha(
                    IndexedColor::BrightBlue,
                    1,
                    2,
                ));
                if !focused {
                    bg = bg.oklab_blend(fb.indexed_alpha(IndexedColor::Background, 1, 2));
                };
                let fg = fb.contrasted(bg);
                fb.blend_bg(rect, bg);
                fb.blend_fg(rect, fg);
            }

            // Nothing to do if the entire line is empty.
            if cursor_beg.offset != cursor_end.offset {
                // If we couldn't reach the left edge, we may have stopped short due to a wide glyph.
                // In that case we'll try to find the next character and then compute by how many
                // columns it overlaps the left edge (can be anything between 1 and 7).
                if cursor_beg.visual_pos.x < origin.x {
                    let cursor_next = self.cursor_move_to_logical_internal(
                        cursor_beg,
                        Point { x: cursor_beg.logical_pos.x + 1, y: cursor_beg.logical_pos.y },
                    );

                    if cursor_next.visual_pos.x > origin.x {
                        let overlap = cursor_next.visual_pos.x - origin.x;
                        debug_assert!((1..=7).contains(&overlap));
                        line.extend_from_slice(&*scratch, &TAB_WHITESPACE[..overlap as usize]);
                        cursor_beg = cursor_next;
                    }
                }

                let mut global_off = cursor_beg.offset;
                let mut cursor_line = cursor_beg;

                while global_off < cursor_end.offset {
                    let chunk = self.read_forward(global_off);
                    let chunk = &chunk[..chunk.len().min(cursor_end.offset - global_off)];
                    let mut off = 0;

                    while off < chunk.len() {
                        let beg = off;
                        off = memchr2(b' ', b'\t', chunk, off);

                        // Anything that isn't whitespace is copied as-is.
                        // The framebuffer takes care of sanitizing it.
                        self.append_visible_text(
                            &scratch,
                            &mut line,
                            &chunk[beg..off],
                            global_off + beg,
                        );

                        while off < chunk.len() && matches!(chunk[off], b' ' | b'\t') {
                            let is_tab = chunk[off] == b'\t';
                            let global_off = global_off + off;
                            if self.hidden_ruby_range(global_off).is_some() {
                                off += 1;
                                continue;
                            }
                            let visualize = selection_off.contains(&global_off);
                            let mut whitespace = TAB_WHITESPACE;
                            let mut prefix_add = 0;

                            if is_tab || visualize {
                                // We need the character's visual position in order to either compute the tab size,
                                // or set the foreground color of the visualizer, respectively.
                                // TODO: Doing this char-by-char is bad for performance.
                                cursor_line =
                                    self.cursor_move_to_offset_internal(cursor_line, global_off);
                            }

                            let tab_size =
                                if is_tab { self.tab_size_eval(cursor_line.column) } else { 1 };

                            if visualize {
                                // If the whitespace is part of the selection,
                                // we replace " " with "･" and "\t" with "￫".
                                (whitespace, prefix_add) = if is_tab {
                                    (VISUAL_TAB, VISUAL_TAB_PREFIX_ADD)
                                } else {
                                    (VISUAL_SPACE, VISUAL_SPACE_PREFIX_ADD)
                                };

                                // Make the visualized characters slightly gray.
                                let visualizer_rect = {
                                    let left = destination.left
                                        + self.margin_width
                                        + cursor_line.visual_pos.x
                                        - origin.x;
                                    let top = destination.top + cursor_line.visual_pos.y - origin.y;
                                    Rect { left, top, right: left + 1, bottom: top + 1 }
                                };
                                fb.blend_fg(
                                    visualizer_rect,
                                    fb.indexed_alpha(IndexedColor::Foreground, 1, 2),
                                );
                            }

                            line.extend_from_slice(
                                &*scratch,
                                &whitespace[..prefix_add + tab_size as usize],
                            );
                            off += 1;
                        }
                    }

                    global_off += chunk.len();
                }

                visual_pos_x_max = visual_pos_x_max.max(cursor_end.visual_pos.x);
            }

            fb.replace_text(destination.top + y, destination.left, destination.right, &line);

            cursor = cursor_end;
        }

        let logical_y_beg = self.cursor_for_rendering.unwrap().logical_pos.y;
        let logical_y_end = cursor.logical_pos.y + 1;
        self.render_apply_highlights(origin, destination, logical_y_beg..logical_y_end, fb);
        self.render_apply_ruby(origin, destination, logical_y_beg..logical_y_end, fb);

        // Colorize the margin that we wrote above.
        if self.margin_width > 0 {
            let margin = Rect {
                left: destination.left,
                top: destination.top,
                right: destination.left + self.margin_width,
                bottom: destination.bottom,
            };
            fb.blend_fg(margin, StraightRgba::from_rgba(0x7f7f7f7f));
        }

        if self.ruler > 0 {
            let left = destination.left + self.margin_width + (self.ruler - origin.x).max(0);
            let right = destination.right;
            if left < right {
                fb.blend_bg(
                    Rect { left, top: destination.top, right, bottom: destination.bottom },
                    fb.indexed_alpha(IndexedColor::BrightRed, 1, 4),
                );
            }
        }

        if focused {
            let mut x = self.cursor.visual_pos.x;
            let mut y = self.cursor.visual_pos.y;

            if self.word_wrap_column > 0 && x >= self.word_wrap_column {
                // The line the cursor is on wraps exactly on the word wrap column which
                // means the cursor is invisible. We need to move it to the next line.
                x = 0;
                y += 1;
            }

            // Move the cursor into screen space.
            x += destination.left - origin.x + self.margin_width;
            y += destination.top - origin.y;

            let cursor = Point { x, y };
            let text = Rect {
                left: destination.left + self.margin_width,
                top: destination.top,
                right: destination.right,
                bottom: destination.bottom,
            };

            if text.contains(cursor) {
                fb.set_cursor(cursor, self.overtype);

                if self.line_highlight_enabled && selection_beg >= selection_end {
                    fb.blend_bg(
                        Rect {
                            left: destination.left,
                            top: cursor.y,
                            right: destination.right,
                            bottom: cursor.y + 1,
                        },
                        StraightRgba::from_rgba(0x7f7f7f7f),
                    );
                }
            }
        }

        self.render_apply_forbidden(origin, destination, logical_y_beg..logical_y_end, fb);

        Some(RenderResult { visual_pos_x_max })
    }

    fn render_apply_forbidden(
        &self,
        origin: Point,
        destination: Rect,
        lines: Range<CoordType>,
        fb: &mut Framebuffer,
    ) {
        if self.forbidden_rules.is_none() || self.word_wrap_column <= 0 {
            return;
        }
        let mut cursor = self.cursor_for_rendering.unwrap();
        let text_left = destination.left + self.margin_width;
        let selection = self.selection_range().map(|(beg, end)| beg.offset..end.offset);
        for y in lines {
            cursor = self.goto_line_start(cursor, y);
            for warning in self.forbidden_line_warnings(cursor).iter() {
                let top = destination.top + warning.pos.y - origin.y;
                if top < destination.top || top >= destination.bottom {
                    continue;
                }
                let left = text_left + warning.pos.x - origin.x;
                let rect = Rect {
                    left: left.max(text_left),
                    top,
                    right: (left + warning.width).min(destination.right),
                    bottom: top + 1,
                };
                if rect.left < rect.right {
                    fb.blend_bg(rect, fb.indexed(IndexedColor::Yellow));
                    fb.blend_fg(rect, fb.indexed(IndexedColor::Red));
                    if let Some(selection) = &selection
                        && warning.source.start < selection.end
                        && warning.source.end > selection.start
                    {
                        fb.replace_attr(rect, Attributes::Underlined, Attributes::Underlined);
                    }
                }
            }
        }
    }

    fn append_visible_text<'a>(
        &self,
        arena: &'a Arena,
        output: &mut BVec<'a, u8>,
        bytes: &[u8],
        offset: usize,
    ) {
        if !self.ruby_display || self.source_is_visible(offset) {
            output.extend_from_slice(arena, bytes);
            return;
        }
        let line = self.ruby_line(offset);
        let end = offset + bytes.len();
        let mut cursor = offset;
        for ruby in &line.ruby {
            for hidden in [ruby.markup.start..ruby.base.start, ruby.base.end..ruby.markup.end] {
                if hidden.end <= cursor || hidden.start >= end {
                    continue;
                }
                if cursor < hidden.start {
                    output.extend_from_slice(arena, &bytes[cursor - offset..hidden.start - offset]);
                }
                cursor = hidden.end.min(end);
            }
        }
        output.extend_from_slice(arena, &bytes[cursor - offset..]);
    }

    fn render_apply_ruby(
        &self,
        origin: Point,
        destination: Rect,
        logical_y_range: Range<CoordType>,
        fb: &mut Framebuffer,
    ) {
        if !self.ruby_display {
            return;
        }
        let text_left = destination.left + self.margin_width;
        let mut cursor = self.cursor_for_rendering.unwrap();
        for y in logical_y_range {
            cursor = self.goto_line_start(cursor, y);
            let line = self.ruby_line(cursor.offset);
            for ruby in &line.ruby {
                let beg = self.cursor_move_to_offset_internal(cursor, ruby.base.start);
                let end = self.cursor_move_to_offset_internal(beg, ruby.base.end);
                for visual_y in beg.visual_pos.y.max(origin.y)
                    ..=end.visual_pos.y.min(origin.y + destination.height() - 1)
                {
                    let left = if visual_y == beg.visual_pos.y { beg.visual_pos.x } else { 0 };
                    let right = if visual_y == end.visual_pos.y {
                        end.visual_pos.x
                    } else {
                        self.word_wrap_column
                    };
                    let rect = Rect {
                        left: (text_left + left - origin.x).max(text_left),
                        right: (text_left + right - origin.x).min(destination.right),
                        top: destination.top + visual_y - origin.y,
                        bottom: destination.top + visual_y - origin.y + 1,
                    };
                    if rect.left < rect.right {
                        fb.blend_fg(rect, fb.indexed(IndexedColor::BrightYellow));
                    }
                }
            }
        }
    }

    fn render_apply_highlights(
        &mut self,
        origin: Point,
        destination: Rect,
        logical_y_range: Range<CoordType>,
        fb: &mut Framebuffer,
    ) {
        let Some(language) = self.language else {
            return;
        };

        let mut highlighter = Highlighter::new(&self.buffer, language);

        // Track cursor position for efficient offset-to-position conversions.
        // Start from the rendering cursor which is at the beginning of the visible area.
        let mut cursor = self.cursor_for_rendering.unwrap();

        // Visible vertical range in visual coordinates.
        let visible_top = origin.y;
        let visible_bottom = origin.y + destination.height();

        // Text area boundaries in screen coordinates (excluding margin).
        let text_left = destination.left + self.margin_width;
        let text_right = destination.right;

        for logical_y in logical_y_range {
            // Seek cursor to the start of this logical line for efficient lookups.
            // This is important because highlights are sorted by offset within
            // each logical line.
            cursor = self.goto_line_start(cursor, logical_y);

            let scratch = scratch_arena(None);
            let highlights =
                self.highlighter_cache.parse_line(&scratch, &mut highlighter, logical_y);

            for pair in highlights.windows(2) {
                let curr = &pair[0];
                let next = &pair[1];

                // Skip highlights with no visual effect.
                if curr.kind == HighlightKind::Other {
                    continue;
                }

                // Convert byte offsets to cursor positions. Since highlights are
                // sorted by offset, we chain from cursor -> beg -> end for efficiency.
                let beg = self.cursor_move_to_offset_internal(cursor, curr.start);
                let end = self.cursor_move_to_offset_internal(beg, next.start);
                cursor = end;

                let color = match curr.kind {
                    HighlightKind::Other => None,
                    HighlightKind::Comment => Some(IndexedColor::Green),
                    HighlightKind::Method => Some(IndexedColor::BrightYellow),
                    HighlightKind::String => Some(IndexedColor::BrightRed),
                    HighlightKind::Variable => Some(IndexedColor::BrightCyan),
                    HighlightKind::ConstantLanguage => Some(IndexedColor::BrightBlue),
                    HighlightKind::ConstantNumeric => Some(IndexedColor::BrightGreen),
                    HighlightKind::KeywordControl => Some(IndexedColor::BrightMagenta),
                    HighlightKind::KeywordOther => Some(IndexedColor::BrightBlue),
                    HighlightKind::KeywordPreprocessor => Some(IndexedColor::BrightBlue),
                    HighlightKind::MarkupBold => None,
                    HighlightKind::MarkupChanged => Some(IndexedColor::BrightBlue),
                    HighlightKind::MarkupDeleted => Some(IndexedColor::BrightRed),
                    HighlightKind::MarkupHeading => Some(IndexedColor::BrightBlue),
                    HighlightKind::MarkupInserted => Some(IndexedColor::BrightGreen),
                    HighlightKind::MarkupItalic => None,
                    HighlightKind::MarkupLink => None,
                    HighlightKind::MarkupList => Some(IndexedColor::BrightBlue),
                    HighlightKind::MarkupStrikethrough => None,
                    HighlightKind::MetaHeader => Some(IndexedColor::BrightBlue),
                    HighlightKind::StorageAnnotation => Some(IndexedColor::Cyan),
                    HighlightKind::StorageType => Some(IndexedColor::Cyan),
                };
                let attr = match curr.kind {
                    HighlightKind::MarkupBold => Some(Attributes::Bold),
                    HighlightKind::MarkupItalic => Some(Attributes::Italic),
                    HighlightKind::MarkupLink => Some(Attributes::Underlined),
                    HighlightKind::MarkupStrikethrough => Some(Attributes::Strikethrough),
                    _ => None,
                };

                // Handle the case where the highlight spans multiple visual lines
                // due to word wrapping. The range is [beg, end) in terms of offsets,
                // which maps to visual lines [beg.visual_pos.y, end.visual_pos.y].
                //
                // When beg and end are on the same visual line, we highlight
                // [beg.visual_pos.x, end.visual_pos.x).
                //
                // When they span multiple lines:
                // - First line: [beg.visual_pos.x, end_of_line)
                // - Middle lines: [0, end_of_line)
                // - Last line: [0, end.visual_pos.x)
                //
                // However, if end.visual_pos.x == 0, the last line has no content
                // to highlight (the span ends exactly at the line boundary).
                let visual_y_end = if end.visual_pos.x == 0 && end.visual_pos.y > beg.visual_pos.y {
                    // The span ends at position 0 of a new visual line, meaning
                    // it actually ends at the end of the previous visual line.
                    end.visual_pos.y - 1
                } else {
                    end.visual_pos.y
                };

                // Use min/max to skip visual lines outside the visible vertical range.
                for visual_y in
                    beg.visual_pos.y.max(visible_top)..(visual_y_end + 1).min(visible_bottom)
                {
                    let vis_left = if visual_y == beg.visual_pos.y {
                        beg.visual_pos.x
                    } else {
                        // Wrapped continuation lines start at visual x=0.
                        0
                    };
                    let vis_right = if visual_y == end.visual_pos.y {
                        end.visual_pos.x
                    } else {
                        // Line extends to the word wrap column or beyond.
                        COORD_TYPE_SAFE_MAX
                    };

                    // Convert to screen coordinates.
                    let screen_left = text_left + vis_left - origin.x;
                    let screen_right = (text_left + vis_right - origin.x).min(text_right);
                    let screen_y = destination.top + visual_y - origin.y;

                    // Create the target rectangle, clamped to the text area.
                    let rect = Rect {
                        left: screen_left.max(text_left),
                        top: screen_y,
                        right: screen_right,
                        bottom: screen_y + 1,
                    };

                    // Skip empty or invalid rectangles.
                    if rect.left >= rect.right {
                        continue;
                    }

                    if let Some(color) = color {
                        fb.blend_fg(rect, fb.indexed(color));
                    }
                    if let Some(attr) = attr {
                        fb.replace_attr(rect, Attributes::All, attr);
                    }
                }
            }
        }
    }

    pub fn cut(&mut self, clipboard: &mut Clipboard) {
        self.cut_copy(clipboard, true);
    }

    pub fn copy(&mut self, clipboard: &mut Clipboard) {
        self.cut_copy(clipboard, false);
    }

    fn cut_copy(&mut self, clipboard: &mut Clipboard, cut: bool) {
        let line_copy = !self.has_selection();
        let selection = self.extract_selection(cut);
        clipboard.write(selection);
        clipboard.write_was_line_copy(line_copy);
    }

    pub fn paste(&mut self, clipboard: &Clipboard, single_line: bool) {
        let data = clipboard.read();

        let data = if single_line {
            // Can't use `unicode::newlines_forward` because bracketed paste uses CR instead of LF/CRLF.
            let off = memchr2(b'\r', b'\n', data, 0);
            unicode::strip_newline(&data[..off])
        } else {
            data
        };

        if data.is_empty() {
            return;
        }

        let pos = self.cursor_logical_pos();
        let at = if clipboard.is_line_copy() {
            self.goto_line_start(self.cursor, pos.y)
        } else {
            self.cursor
        };

        self.write(data, at, true);

        if clipboard.is_line_copy() {
            self.cursor_move_to_logical(Point { x: pos.x, y: pos.y + 1 });
        }
    }

    /// Inserts the user input `text` at the current cursor position.
    /// Replaces tabs with whitespace if needed, etc.
    pub fn write_canon(&mut self, text: &[u8]) {
        self.write(text, self.cursor, false);
    }

    /// Inserts `text` as-is at the current cursor position.
    /// The only transformation applied is that newlines are normalized.
    pub fn write_raw(&mut self, text: &[u8]) {
        self.write(text, self.cursor, true);
    }

    fn write(&mut self, text: &[u8], at: Cursor, raw: bool) {
        if self.is_format_editing() && text.iter().any(|byte| matches!(byte, b'\r' | b'\n')) {
            return;
        }
        let at = self.constrain_format_cursor(at);
        let history_type = if raw { HistoryType::Other } else { HistoryType::Write };
        let mut edit_begun = false;

        // If we have an active selection, writing an empty `text`
        // will still delete the selection. As such, we check this first.
        if let Some((beg, end)) = self.selection_range_internal(false) {
            self.edit_begin(history_type, beg);
            self.edit_delete(end);
            self.set_selection(None);
            edit_begun = true;
        }

        // If the text is empty the remaining code won't do anything,
        // allowing us to exit early.
        if text.is_empty() {
            // ...we still need to end any active edit session though.
            if edit_begun {
                self.edit_end();
            }
            return;
        }

        if !edit_begun {
            let at = self.ruby_insertion_cursor(at);
            self.edit_begin(history_type, at);
        }

        let mut offset = 0;
        let scratch = scratch_arena(None);
        let mut newline_buffer = BString::empty();

        loop {
            // Can't use `unicode::newlines_forward` because bracketed paste uses CR instead of LF/CRLF.
            let offset_next = memchr2(b'\r', b'\n', text, offset);
            let line = &text[offset..offset_next];
            let column_before = self.cursor.logical_pos.x;

            // Write the contents of the line into the buffer.
            let mut line_off = 0;
            while line_off < line.len() {
                // Split the line into chunks of non-tabs and tabs.
                let mut plain = line;
                if !raw && !self.indent_with_tabs {
                    let end = memchr2(b'\t', b'\t', line, line_off);
                    plain = &line[line_off..end];
                }

                // Non-tabs are written as-is, because the outer loop already handles newline translation.
                self.edit_write(plain);
                line_off += plain.len();

                // Now replace tabs with spaces.
                while line_off < line.len() && line[line_off] == b'\t' {
                    let spaces = self.tab_size_eval(self.cursor.column);
                    let spaces = &TAB_WHITESPACE[..spaces as usize];
                    self.edit_write(spaces);
                    line_off += 1;
                }
            }

            if !raw && self.overtype {
                let delete = self.cursor.logical_pos.x - column_before;
                let end = self.cursor_move_to_logical_internal(
                    self.cursor,
                    Point { x: self.cursor.logical_pos.x + delete, y: self.cursor.logical_pos.y },
                );
                self.edit_delete(end);
            }

            offset += line.len();
            if offset >= text.len() {
                break;
            }

            // First, write the newline.
            newline_buffer.clear();
            newline_buffer.push_str(&*scratch, if self.newlines_are_crlf { "\r\n" } else { "\n" });

            if !raw {
                // We'll give the next line the same indentation as the previous one.
                // This block figures out how much that is. We can't reuse that value,
                // because "  a\n  a\n" should give the 3rd line a total indentation of 4.
                // Assuming your terminal has bracketed paste, this won't be a concern though.
                // (If it doesn't, use a different terminal.)
                let line_beg = self.goto_line_start(self.cursor, self.cursor.logical_pos.y);
                let limit = self.cursor.offset;
                let mut off = line_beg.offset;
                let mut newline_indentation = 0;

                'outer: while off < limit {
                    let chunk = self.read_forward(off);
                    let chunk = &chunk[..chunk.len().min(limit - off)];

                    for &c in chunk {
                        if c == b' ' {
                            newline_indentation += 1;
                        } else if c == b'\t' {
                            newline_indentation += self.tab_size_eval(newline_indentation);
                        } else {
                            break 'outer;
                        }
                    }

                    off += chunk.len();
                }

                // If tabs are enabled, add as many tabs as we can.
                if self.indent_with_tabs {
                    let tab_count = newline_indentation / self.tab_size;
                    newline_buffer.push_repeat(&*scratch, '\t', tab_count as usize);
                    newline_indentation -= tab_count * self.tab_size;
                }

                // If tabs are disabled, or if the indentation wasn't a multiple of the tab size,
                // add spaces to make up the difference.
                newline_buffer.push_repeat(&*scratch, ' ', newline_indentation as usize);
            }

            self.edit_write(newline_buffer.as_bytes());

            // Skip one CR/LF/CRLF.
            if offset >= text.len() {
                break;
            }
            if text[offset] == b'\r' {
                offset += 1;
            }
            if offset >= text.len() {
                break;
            }
            if text[offset] == b'\n' {
                offset += 1;
            }
            if offset >= text.len() {
                break;
            }
        }

        // POSIX mandates that all valid lines end in a newline.
        // This isn't all that common on Windows and so we have
        // `self.final_newline` to control this.
        //
        // In order to not annoy people with this, we only add a
        // newline if you just edited the very end of the buffer.
        if !self.is_format_editing()
            && self.insert_final_newline
            && self.cursor.offset > 0
            && self.cursor.offset == self.text_length()
            && self.cursor.logical_pos.x > 0
        {
            let cursor = self.cursor;
            self.edit_write(if self.newlines_are_crlf { b"\r\n" } else { b"\n" });
            // Can't use `set_cursor_internal` here, because we haven't updated the line stats yet.
            self.cursor = cursor;
        }

        self.edit_end();
    }

    /// Deletes 1 grapheme cluster from the buffer.
    /// `cursor_movements` is expected to be -1 for backspace and 1 for delete.
    /// If there's a current selection, it will be deleted and `cursor_movements` ignored.
    /// The selection is cleared after the call.
    /// Deletes characters from the buffer based on a delta from the cursor.
    pub fn delete(&mut self, granularity: CursorMovement, delta: CoordType) {
        if delta == 0 {
            return;
        }
        self.finish_selection_latch();

        let mut beg;
        let mut end;

        if let Some(r) = self.selection_range_internal(false) {
            (beg, end) = r;
        } else {
            if (delta < 0 && self.cursor.offset == 0)
                || (delta > 0 && self.cursor.offset >= self.text_length())
            {
                // Nothing to delete.
                return;
            }

            beg = self.cursor;
            end = self.cursor_move_delta_internal(beg, granularity, delta);
            if beg.offset == end.offset {
                return;
            }
            if beg.offset > end.offset {
                mem::swap(&mut beg, &mut end);
            }
        }

        (beg, end) = self.ruby_source_range(beg, end);
        if beg.offset == end.offset {
            return;
        }

        self.edit_begin(HistoryType::Delete, beg);
        self.edit_delete(end);
        self.edit_end();

        self.set_selection(None);
    }

    /// Returns the logical position of the first character on this line.
    /// Return `.x == 0` if there are no non-whitespace characters.
    pub fn indent_end_logical_pos(&self) -> Point {
        let cursor = self.goto_line_start(self.cursor, self.cursor.logical_pos.y);
        let (chars, _) = self.measure_indent_internal(cursor.offset, CoordType::MAX);
        Point { x: chars, y: cursor.logical_pos.y }
    }

    /// Indents/unindents the current selection or line.
    pub fn indent_change(&mut self, direction: CoordType) {
        let selection = self.selection;
        let mut selection_beg = self.cursor.logical_pos;
        let mut selection_end = selection_beg;

        if let Some(TextBufferSelection { beg, end }) = &selection {
            selection_beg = *beg;
            selection_end = *end;
        }

        if direction >= 0 && self.selection.is_none_or(|sel| sel.beg.y == sel.end.y) {
            self.write_canon(b"\t");
            return;
        }

        self.edit_begin_grouping();

        for y in selection_beg.y.min(selection_end.y)..=selection_beg.y.max(selection_end.y) {
            self.cursor_move_to_logical(Point { x: 0, y });

            let line_start_offset = self.cursor.offset;
            let (curr_chars, curr_columns) =
                self.measure_indent_internal(line_start_offset, CoordType::MAX);

            self.cursor_move_to_logical(Point { x: curr_chars, y: self.cursor.logical_pos.y });

            let delta;

            if direction < 0 {
                // Unindent the line. If there's no indentation, skip.
                if curr_columns <= 0 {
                    continue;
                }

                let (prev_chars, _) = self.measure_indent_internal(
                    line_start_offset,
                    self.tab_size_prev_column(curr_columns),
                );

                delta = prev_chars - curr_chars;
                self.delete(CursorMovement::Grapheme, delta);
            } else {
                // Indent the line. `self.cursor` is already at the level of indentation.
                delta = self.tab_size_eval(curr_columns);
                self.write_canon(b"\t");
            }

            // As the lines get unindented, the selection should shift with them.
            if y == selection_beg.y {
                selection_beg.x += delta;
            }
            if y == selection_end.y {
                selection_end.x += delta;
            }
        }
        self.edit_end_grouping();

        // Move the cursor to the new end of the selection.
        self.set_cursor_internal(self.cursor_move_to_logical_internal(self.cursor, selection_end));

        // NOTE: If the selection was previously `None`,
        // it should continue to be `None` after this.
        self.set_selection(
            selection.map(|_| TextBufferSelection { beg: selection_beg, end: selection_end }),
        );
    }

    fn measure_indent_internal(
        &self,
        mut offset: usize,
        max_columns: CoordType,
    ) -> (CoordType, CoordType) {
        let mut chars = 0;
        let mut columns = 0;

        'outer: loop {
            let chunk = self.read_forward(offset);
            if chunk.is_empty() {
                break;
            }

            for &c in chunk {
                let next = match c {
                    b' ' => columns + 1,
                    b'\t' => columns + self.tab_size_eval(columns),
                    _ => break 'outer,
                };
                if next > max_columns {
                    break 'outer;
                }
                chars += 1;
                columns = next;
            }

            offset += chunk.len();

            // No need to do another round if we
            // already got the exact right amount.
            if columns >= max_columns {
                break;
            }
        }

        (chars, columns)
    }

    /// Displaces the current, cursor or the selection, line(s) in the given direction.
    pub fn move_selected_lines(&mut self, direction: MoveLineDirection) {
        if self.is_format_editing() {
            return;
        }
        let selection = self.selection;
        let cursor = self.cursor;

        // If there's no selection, we move the line the cursor is on instead.
        let [beg, end] = match self.selection {
            Some(s) => minmax(s.beg.y, s.end.y),
            None => [cursor.logical_pos.y, cursor.logical_pos.y],
        };

        // Check if this would be a no-op.
        if match direction {
            MoveLineDirection::Up => beg <= 0,
            MoveLineDirection::Down => end >= self.stats.logical_lines - 1,
        } {
            return;
        }

        let delta = match direction {
            MoveLineDirection::Up => -1,
            MoveLineDirection::Down => 1,
        };
        let (cut, paste) = match direction {
            MoveLineDirection::Up => (beg - 1, end),
            MoveLineDirection::Down => (end + 1, beg),
        };

        self.edit_begin_grouping();
        {
            // Let's say this is `MoveLineDirection::Up`.
            // In that case, we'll cut (remove) the line above the selection here...
            self.cursor_move_to_logical(Point { x: 0, y: cut });
            let line = self.extract_selection(true);

            // ...and paste it below the selection. This will then
            // appear to the user as if the selection was moved up.
            self.cursor_move_to_logical(Point { x: 0, y: paste });
            self.edit_begin(HistoryType::Write, self.cursor);
            // The `extract_selection` call can return an empty `Vec`),
            // if the `cut` line was at the end of the file. Since we want to
            // paste the line somewhere it needs a trailing newline at the minimum.
            //
            // Similarly, if the `paste` line is at the end of the file
            // and there's no trailing newline, we'll have failed to reach
            // that end in which case `logical_pos.y != past`.
            if line.is_empty() || self.cursor.logical_pos.y != paste {
                self.write_canon(b"\n");
            }
            if !line.is_empty() {
                self.write_raw(&line);
            }
            self.edit_end();
        }
        self.edit_end_grouping();

        // Shift the cursor and selection together with the moved lines.
        self.cursor_move_to_logical(Point {
            x: cursor.logical_pos.x,
            y: cursor.logical_pos.y + delta,
        });
        self.set_selection(selection.map(|mut s| {
            s.beg.y += delta;
            s.end.y += delta;
            s
        }));
    }

    /// Extracts the contents of the current selection.
    /// May optionally delete it, if requested. This is meant to be used for Ctrl+X.
    fn extract_selection(&mut self, delete: bool) -> Vec<u8> {
        let line_copy = !self.has_selection();
        let Some((beg, end)) = self.selection_range_internal(true) else {
            return Vec::new();
        };

        let mut out = Vec::new();
        self.buffer.extract_raw(beg.offset..end.offset, &mut out, 0);

        if delete && !out.is_empty() {
            self.edit_begin(HistoryType::Delete, beg);
            self.edit_delete(end);
            self.edit_end();
            self.set_selection(None);
        }

        // Line copies (= Ctrl+C when there's no selection) always end with a newline.
        if line_copy && !out.ends_with(b"\n") {
            out.replace_range(out.len().., if self.newlines_are_crlf { b"\r\n" } else { b"\n" });
        }

        out
    }

    /// Extracts the contents of the current selection the user made.
    /// This differs from `TextBuffer::extract_selection()` in that
    /// it does nothing if the selection was made by searching.
    pub fn extract_user_selection(&mut self, delete: bool) -> Option<Vec<u8>> {
        if !self.has_selection() {
            return None;
        }

        if let Some(search) = &self.search {
            let search = unsafe { &*search.get() };
            if search.selection_generation == self.selection_generation {
                return None;
            }
        }

        Some(self.extract_selection(delete))
    }

    /// Returns the current selection anchors, or `None` if there
    /// is no selection. The returned logical positions are sorted.
    pub fn selection_range(&self) -> Option<(Cursor, Cursor)> {
        self.selection_range_internal(false)
    }

    /// Returns the current selection anchors.
    ///
    /// If there's no selection and `line_fallback` is `true`,
    /// the start/end of the current line are returned.
    /// This is meant to be used for Ctrl+C / Ctrl+X.
    fn selection_range_internal(&self, line_fallback: bool) -> Option<(Cursor, Cursor)> {
        let [beg, end] = match self.selection {
            None if !line_fallback => return None,
            None => [
                Point { x: 0, y: self.cursor.logical_pos.y },
                Point { x: 0, y: self.cursor.logical_pos.y + 1 },
            ],
            Some(TextBufferSelection { beg, end }) => minmax(beg, end),
        };

        let beg = self.cursor_move_to_logical_internal(self.cursor, beg);
        let end = self.cursor_move_to_logical_internal(beg, end);

        let (beg, end) = self.ruby_source_range(beg, end);
        if beg.offset < end.offset { Some((beg, end)) } else { None }
    }

    fn edit_begin_grouping(&mut self) {
        self.active_edit_group = Some(ActiveEditGroupInfo {
            cursor_before: self.cursor.logical_pos,
            selection_before: self.selection,
            stats_before: self.stats,
            generation_before: self.buffer.generation(),
        });
    }

    fn edit_end_grouping(&mut self) {
        self.active_edit_group = None;
    }

    /// Starts a new edit operation.
    /// This is used for tracking the undo/redo history.
    fn edit_begin(&mut self, history_type: HistoryType, cursor: Cursor) {
        self.finish_selection_latch();
        self.active_edit_depth += 1;
        if self.active_edit_depth > 1 {
            return;
        }

        let cursor_before = self.cursor;
        self.set_cursor_internal(cursor);

        // If both the last and this are a Write/Delete operation, we skip allocating a new undo history item.
        if history_type != self.last_history_type
            || !matches!(history_type, HistoryType::Write | HistoryType::Delete)
        {
            self.redo_stack.clear();
            while self.undo_stack.len() > 1000 {
                self.undo_stack.pop_front();
                if let Some(edit) = &mut self.format_edit {
                    edit.undo_floor = edit.undo_floor.saturating_sub(1);
                }
            }

            self.last_history_type = history_type;
            self.undo_stack.push_back(SemiRefCell::new(HistoryEntry {
                cursor_before: cursor_before.logical_pos,
                selection_before: self.selection,
                stats_before: self.stats,
                generation_before: self.buffer.generation(),
                cursor: cursor.logical_pos,
                deleted: Vec::new(),
                added: Vec::new(),
                format_wraps_before: self.format_edit.as_ref().map(|edit| edit.wraps.clone()),
            }));

            if let Some(info) = &self.active_edit_group
                && let Some(entry) = self.undo_stack.back()
            {
                let mut entry = entry.borrow_mut();
                entry.cursor_before = info.cursor_before;
                entry.selection_before = info.selection_before;
                entry.stats_before = info.stats_before;
                entry.generation_before = info.generation_before;
            }
        }

        self.active_edit_off = cursor.offset;
        if let Some(edit) = &mut self.format_edit {
            edit.undone = 0;
        }
        self.highlighter_cache.invalidate_from(cursor.logical_pos.y);

        // If word-wrap is enabled, the visual layout of all logical lines affected by the write
        // may have changed. This includes even text before the insertion point up to the line
        // start, because this write may have joined with a word before the initial cursor.
        // See other uses of `word_wrap_cursor_next_line` in this function.
        if self.word_wrap_column > 0 || self.ruby_display {
            let safe_start = self.goto_line_start(cursor, cursor.logical_pos.y);
            let next_line = self.cursor_move_to_logical_internal(
                cursor,
                Point { x: 0, y: cursor.logical_pos.y + 1 },
            );
            self.active_edit_line_info = Some(ActiveEditLineInfo {
                safe_start,
                line_height_in_rows: next_line.visual_pos.y - safe_start.visual_pos.y,
                distance_next_line_start: next_line.offset - cursor.offset,
            });
        }
    }

    /// Writes `text` into the buffer at the current cursor position.
    /// It records the change in the undo stack.
    fn edit_write(&mut self, text: &[u8]) {
        let logical_y_before = self.cursor.logical_pos.y;

        // Copy the written portion into the undo entry.
        {
            let mut undo = self.undo_stack.back_mut().unwrap().borrow_mut();
            undo.added.extend_from_slice(text);
        }

        // Write!
        self.buffer.replace(self.active_edit_off..self.active_edit_off, text);
        self.update_format_offsets(self.active_edit_off..self.active_edit_off, text.len());

        // Move self.cursor to the end of the newly written text. Can't use `self.set_cursor_internal`,
        // because we're still in the progress of recalculating the line stats.
        self.active_edit_off += text.len();
        self.cursor = self.cursor_move_to_offset_internal(self.cursor, self.active_edit_off);
        self.stats.logical_lines += self.cursor.logical_pos.y - logical_y_before;
    }

    /// Deletes the text between the current cursor position and `to`.
    /// It records the change in the undo stack.
    fn edit_delete(&mut self, to: Cursor) {
        let to = self.constrain_format_cursor(to);
        debug_assert!(to.offset >= self.active_edit_off);

        let logical_y_before = self.cursor.logical_pos.y;
        let off = self.active_edit_off;
        let mut out_off = usize::MAX;

        let mut undo = self.undo_stack.back_mut().unwrap().borrow_mut();

        // If this is a continued backspace operation,
        // we need to prepend the deleted portion to the undo entry.
        if self.cursor.logical_pos < undo.cursor {
            out_off = 0;
            undo.cursor = self.cursor.logical_pos;
        }

        // Copy the deleted portion into the undo entry.
        let deleted = &mut undo.deleted;
        self.buffer.extract_raw(off..to.offset, deleted, out_off);

        // Delete the portion from the buffer by enlarging the gap.
        let count = to.offset - off;
        self.buffer.allocate_gap(off, 0, count);

        drop(undo);
        self.update_format_offsets(off..to.offset, 0);

        self.stats.logical_lines += logical_y_before - to.logical_pos.y;
    }

    /// Finalizes the current edit operation
    /// and recalculates the line statistics.
    fn edit_end(&mut self) {
        self.active_edit_depth -= 1;
        debug_assert!(self.active_edit_depth >= 0);
        if self.active_edit_depth > 0 {
            return;
        }

        #[cfg(debug_assertions)]
        {
            let entry = self.undo_stack.back_mut().unwrap().borrow_mut();
            debug_assert!(!entry.deleted.is_empty() || !entry.added.is_empty());
        }

        if let Some(info) = self.active_edit_line_info.take() {
            let deleted_count = self.undo_stack.back_mut().unwrap().borrow_mut().deleted.len();
            let target = self.cursor.logical_pos;

            // From our safe position we can measure the actual visual position of the cursor.
            // Newlines may have increased the visual row count. Install the
            // measured cursor before updating that count, as in undo_redo().
            self.cursor = self.cursor_move_to_logical_internal(info.safe_start, target);

            // If content is added at the insertion position, that's not a problem:
            // We can just remeasure the height of this one line and calculate the delta.
            // `deleted_count` is 0 in this case.
            //
            // The problem is when content is deleted, because it may affect lines
            // beyond the end of the `next_line`. In that case we have to measure
            // the entire buffer contents until the end to compute `self.stats.visual_lines`.
            if deleted_count < info.distance_next_line_start {
                // Now we can measure how many more visual rows this logical line spans.
                let next_line = self
                    .cursor_move_to_logical_internal(self.cursor, Point { x: 0, y: target.y + 1 });
                let lines_before = info.line_height_in_rows;
                let lines_after = next_line.visual_pos.y - info.safe_start.visual_pos.y;
                self.stats.visual_lines += lines_after - lines_before;
            } else {
                let end = self.cursor_move_to_logical_internal(self.cursor, Point::MAX);
                self.stats.visual_lines = end.visual_pos.y + 1;
            }
        } else {
            // If word-wrap is disabled the visual line count always matches the logical one.
            self.stats.visual_lines = self.stats.logical_lines;
        }

        self.recalc_after_content_changed();
    }

    /// Undo the last edit operation.
    pub fn undo(&mut self) {
        self.undo_redo(true);
    }

    /// Redo the last undo operation.
    pub fn redo(&mut self) {
        self.undo_redo(false);
    }

    fn undo_redo(&mut self, undo: bool) {
        let buffer_generation = self.buffer.generation();
        let mut entry_buffer_generation = None;
        let mut damage_start = CoordType::MAX;

        loop {
            if let Some(edit) = &self.format_edit {
                if (undo && self.undo_stack.len() <= edit.undo_floor) || (!undo && edit.undone == 0)
                {
                    break;
                }
            }
            // Transfer the last entry from the undo stack to the redo stack or vice versa.
            {
                let (from, to) = if undo {
                    (&mut self.undo_stack, &mut self.redo_stack)
                } else {
                    (&mut self.redo_stack, &mut self.undo_stack)
                };

                // Only pop the entry if its buffer generation matches the previous one
                let Some(g) = from.pop_back_if(|c| {
                    entry_buffer_generation.is_none_or(|g| g == c.borrow().generation_before)
                }) else {
                    break;
                };

                to.push_back(g);
            }
            if let Some(edit) = &mut self.format_edit {
                if undo {
                    edit.undone += 1;
                } else {
                    edit.undone -= 1;
                }
            }

            self.finish_selection_latch();

            let change = {
                let to = if undo { &self.redo_stack } else { &self.undo_stack };
                to.back().unwrap()
            };

            // Remember the buffer generation of the change so we can stop popping undos/redos.
            // Also, move to the point where the modification took place.
            let cursor = {
                let change = change.borrow();
                entry_buffer_generation = Some(change.generation_before);
                self.cursor_move_to_logical_internal(self.cursor, change.cursor)
            };

            let safe_cursor = if self.word_wrap_column > 0 || self.ruby_display {
                // If word-wrap is enabled, we need to move the cursor to the beginning of the line.
                // This is because the undo/redo operation may have changed the visual position of the cursor.
                self.goto_line_start(cursor, cursor.logical_pos.y)
            } else {
                cursor
            };

            damage_start = damage_start.min(cursor.logical_pos.y);

            {
                let mut change = change.borrow_mut();
                let change = &mut *change;

                // Undo: Whatever was deleted is now added and vice versa.
                mem::swap(&mut change.deleted, &mut change.added);
                if let Some(edit) = &mut self.format_edit {
                    let wraps = edit.wraps.clone();
                    edit.replace(
                        cursor.offset..cursor.offset + change.deleted.len(),
                        change.added.len(),
                    );
                    if let Some(previous) = &mut change.format_wraps_before {
                        edit.wraps = mem::replace(previous, wraps);
                    }
                }

                // Delete the inserted portion.
                self.buffer.allocate_gap(cursor.offset, 0, change.deleted.len());

                // Reinsert the deleted portion.
                {
                    let added = &change.added[..];
                    let mut beg = 0;
                    let mut offset = cursor.offset;

                    while beg < added.len() {
                        let (end, line) = simd::lines_fwd(added, beg, 0, 1);
                        let has_newline = line != 0;
                        let link = &added[beg..end];
                        let line = unicode::strip_newline(link);
                        let mut written;

                        {
                            let gap = self.buffer.allocate_gap(offset, line.len() + 2, 0);
                            written = slice_copy_safe(gap, line);

                            if has_newline {
                                if self.newlines_are_crlf && written < gap.len() {
                                    gap[written] = b'\r';
                                    written += 1;
                                }
                                if written < gap.len() {
                                    gap[written] = b'\n';
                                    written += 1;
                                }
                            }

                            self.buffer.commit_gap(written);
                        }

                        beg = end;
                        offset += written;
                    }
                }

                // Restore the previous line statistics.
                mem::swap(&mut self.stats, &mut change.stats_before);

                // Restore the previous selection.
                mem::swap(&mut self.selection, &mut change.selection_before);

                // Pretend as if the buffer was never modified.
                self.buffer.set_generation(change.generation_before);
                change.generation_before = buffer_generation;

                // Restore the previous cursor.
                let cursor_before =
                    self.cursor_move_to_logical_internal(safe_cursor, change.cursor_before);
                change.cursor_before = self.cursor.logical_pos;
                // Can't use `set_cursor_internal` here, because we haven't updated the line stats yet.
                self.cursor = cursor_before;

                if self.undo_stack.is_empty() {
                    self.last_history_type = HistoryType::Other;
                }
            }
        }

        if damage_start == CoordType::MAX {
            // There weren't any undo/redo entries.
            return;
        }

        self.highlighter_cache.invalidate_from(damage_start);

        if entry_buffer_generation.is_some() {
            self.recalc_after_content_changed();
            if self.is_format_editing() {
                self.last_history_type = HistoryType::Other;
                self.reflow();
            }
        }
    }

    /// For interfacing with ICU.
    pub(crate) fn read_backward(&self, off: usize) -> &[u8] {
        self.buffer.read_backward(off)
    }

    /// For interfacing with ICU.
    pub fn read_forward(&self, off: usize) -> &[u8] {
        self.buffer.read_forward(off)
    }
}

pub enum Bom {
    None,
    UTF8,
    UTF16LE,
    UTF16BE,
    UTF32LE,
    UTF32BE,
    GB18030,
}

const BOM_MAX_LEN: usize = 4;

fn detect_bom(bytes: &[u8]) -> Option<&'static str> {
    if bytes.len() >= 4 {
        if bytes.starts_with(b"\xFF\xFE\x00\x00") {
            return Some("UTF-32LE");
        }
        if bytes.starts_with(b"\x00\x00\xFE\xFF") {
            return Some("UTF-32BE");
        }
        if bytes.starts_with(b"\x84\x31\x95\x33") {
            return Some("GB18030");
        }
    }
    if bytes.len() >= 3 && bytes.starts_with(b"\xEF\xBB\xBF") {
        return Some("UTF-8");
    }
    if bytes.len() >= 2 {
        if bytes.starts_with(b"\xFF\xFE") {
            return Some("UTF-16LE");
        }
        if bytes.starts_with(b"\xFE\xFF") {
            return Some("UTF-16BE");
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::{CursorMovement, SearchOptions, TextBuffer};
    use crate::framebuffer::Framebuffer;
    use crate::helpers::{Point, Rect, Size};
    use stdext::arena::scratch_arena;

    fn buffer_contents(buf: &mut TextBuffer) -> String {
        let mut str = String::new();
        buf.save_as_string(&mut str);
        str
    }

    fn ruby_buffer(text: &str) -> TextBuffer {
        let mut buf = TextBuffer::new(false).unwrap();
        buf.set_crlf(false);
        buf.set_ruby_display(true);
        buf.write_raw(text.as_bytes());
        buf.set_width(80);
        buf.cursor_move_to_logical(Point::default());
        buf
    }

    fn forbidden_buffer(text: &str, width: isize, sequences: &[&str]) -> TextBuffer {
        let mut buf = ruby_buffer(text);
        buf.set_forbidden_rules(Some(std::rc::Rc::new(super::ForbiddenRules {
            line_start: "、。（".to_string(),
            line_end: "（".to_string(),
            paragraph_start_allowed: "（".to_string(),
            inseparable: sequences.iter().map(|text| text.to_string()).collect(),
        })));
        buf.set_wrap_chars(Some(width));
        buf.set_word_wrap(true);
        buf.set_width(80);
        buf
    }

    #[test]
    fn forbidden_heads_tails_and_paragraph_exception_follow_display_rows() {
        let source = "あい、う\nあ（いう\n（あいう";
        let mut buf = forbidden_buffer(source, 2, &[]);
        buf.cursor_move_to_offset("あい".len());
        assert!(buf.forbidden_warning_at_cursor().unwrap().contains("行頭禁則"));
        let start = buf.goto_line_start(buf.cursor, 0);
        let warnings = buf.forbidden_line_warnings(start);
        assert_eq!(warnings.len(), 1);
        assert_eq!(warnings[0].pos, Point { x: 0, y: 1 });
        assert_eq!(warnings[0].width, 2);
        buf.cursor_move_to_offset("あい、う\nあ".len());
        assert!(buf.forbidden_warning_at_cursor().unwrap().contains("行末禁則"));
        buf.cursor_move_to_offset("あい、う\nあ（いう\n".len());
        assert_eq!(buf.forbidden_warning_at_cursor(), None);
        assert_eq!(buffer_contents(&mut buf), source);
        buf.set_word_wrap(false);
        buf.set_width(80);
        buf.cursor_move_to_offset("あい".len());
        assert_eq!(buf.forbidden_warning_at_cursor(), None);
    }

    #[test]
    fn forbidden_sequences_recompute_after_resize_edits_and_undo() {
        let mut buf = forbidden_buffer("aAB", 2, &["AB"]);
        let start = buf.goto_line_start(buf.cursor, 0);
        assert!(buf.forbidden_line_warnings(start).is_empty());
        buf.set_width(2);
        let warnings = buf.forbidden_line_warnings(start);
        assert_eq!(warnings.len(), 2);
        assert_eq!(warnings[0].pos, Point { x: 1, y: 0 });
        assert_eq!(warnings[1].pos, Point { x: 0, y: 1 });
        buf.write_canon(b"a");
        let start = buf.goto_line_start(buf.cursor, 0);
        assert!(buf.forbidden_line_warnings(start).is_empty());
        buf.undo();
        let start = buf.goto_line_start(buf.cursor, 0);
        assert_eq!(buf.forbidden_line_warnings(start).len(), 2);
        buf.set_width(80);
        let start = buf.goto_line_start(buf.cursor, 0);
        assert!(buf.forbidden_line_warnings(start).is_empty());
    }

    #[test]
    fn forbidden_sequences_include_overlaps_and_combining_clusters() {
        let buf = forbidden_buffer("aaa", 1, &["aa"]);
        let warnings = buf.forbidden_line_warnings(buf.goto_line_start(buf.cursor, 0));
        assert_eq!(warnings.len(), 2);
        assert_eq!(warnings[0].source, 1..2);
        assert_eq!(warnings[1].source, 2..3);
        let buf = forbidden_buffer("か\u{3099}い", 1, &["か\u{3099}い"]);
        let warnings = buf.forbidden_line_warnings(buf.goto_line_start(buf.cursor, 0));
        assert_eq!(warnings.len(), 2);
        assert_eq!(warnings[0].source, 0.."か\u{3099}".len());
        assert!(warnings.iter().all(|warning| warning.width == 2));
    }

    #[test]
    fn forbidden_uses_annotation_bases_and_ignores_hidden_readings() {
        let mut buf = forbidden_buffer("あ｜漢字《、》う\n《《あい》》、う", 2, &[]);
        let warnings = buf.forbidden_line_warnings(buf.goto_line_start(buf.cursor, 0));
        assert_eq!(warnings.len(), 2);
        assert!(
            warnings
                .iter()
                .all(|warning| warning.reasons.iter().all(|reason| reason.contains("ルビの母字")))
        );
        buf.cursor_move_to_offset("あ｜漢字《、》う\n《《あい》》".len());
        assert!(buf.forbidden_warning_at_cursor().unwrap().contains("行頭禁則"));
    }

    #[test]
    fn selection_latch_requires_both_ctrl_and_shift_in_terminal_input() {
        use crate::input::{self, kbmod, vk};
        let mut buf = ruby_buffer("abcdef");
        for (suffix, arrow) in [('A', vk::UP), ('B', vk::DOWN), ('C', vk::RIGHT), ('D', vk::LEFT)] {
            // xterm modifiers: none, Shift, Alt, Alt+Shift, Ctrl, Ctrl+Shift,
            // Ctrl+Alt, and Ctrl+Alt+Shift, respectively.
            for modifier in 1..=8 {
                buf.clear_selection();
                let sequence = format!("\x1b[1;{modifier}{suffix}");
                let mut vt = crate::vt::Parser::new();
                let mut parser = input::Parser::new();
                let mut events = parser.parse(vt.parse(&sequence));
                let Some(input::Input::Keyboard(key)) = events.next() else {
                    panic!("failed to decode {sequence:?}");
                };
                let mapped = buf.selection_latch_key(key);
                let starts_latch = matches!(modifier, 6 | 8);
                assert_eq!(buf.is_selection_latched(), starts_latch, "{sequence:?}");
                assert!(mapped == Some(if starts_latch { kbmod::SHIFT | arrow } else { key }));
            }
        }
    }

    #[test]
    fn selection_latch_starts_with_one_step_and_keeps_its_anchor() {
        use crate::input::{kbmod, vk};
        let mut buf = ruby_buffer("abcdef");
        buf.cursor_move_to_logical(Point { x: 3, y: 0 });
        assert!(
            buf.selection_latch_key(kbmod::CTRL_SHIFT | vk::RIGHT)
                == Some(kbmod::SHIFT | vk::RIGHT)
        );
        buf.selection_update_delta(CursorMovement::Grapheme, 1);
        assert_eq!(buf.extract_user_selection(false).unwrap(), b"d");
        assert!(buf.selection_latch_key(vk::LEFT) == Some(kbmod::SHIFT | vk::LEFT));
        buf.selection_update_delta(CursorMovement::Grapheme, -1);
        assert!(!buf.has_selection());
        assert!(buf.is_selection_latched());
        buf.selection_update_delta(CursorMovement::Grapheme, -1);
        assert_eq!(buf.extract_user_selection(false).unwrap(), b"c");
        buf.selection_latch_key(kbmod::CTRL_SHIFT | vk::RIGHT);
        buf.selection_update_delta(CursorMovement::Grapheme, 2);
        assert_eq!(buf.extract_user_selection(false).unwrap(), b"d");
        assert!(buf.selection_latch_key(vk::HOME) == Some(kbmod::SHIFT | vk::HOME));
    }

    #[test]
    fn selection_latch_enter_confirms_and_escape_clears() {
        use crate::input::vk;
        let mut buf = ruby_buffer("｜漢字《かんじ》《《圏点》》");
        buf.start_selection_latch();
        buf.selection_update_delta(CursorMovement::Grapheme, 2);
        assert_eq!(buf.extract_user_selection(false).unwrap(), "｜漢字《かんじ》".as_bytes());
        assert!(buf.selection_latch_key(vk::RETURN).is_none());
        assert!(!buf.is_selection_latched());
        assert!(buf.has_selection());
        assert!(buf.selection_latch_key(vk::RIGHT) == Some(vk::RIGHT));
        assert_eq!(buffer_contents(&mut buf), "｜漢字《かんじ》《《圏点》》");
        buf.start_selection_latch();
        buf.selection_update_delta(CursorMovement::Grapheme, 1);
        assert!(buf.selection_latch_key(vk::ESCAPE).is_none());
        assert!(!buf.is_selection_latched());
        assert!(!buf.has_selection());
    }

    #[test]
    fn selection_latch_survives_copy_save_and_unknown_keys() {
        use crate::input::{kbmod, vk};
        let mut buf = ruby_buffer("abcdef");
        buf.start_selection_latch();
        buf.selection_update_delta(CursorMovement::Grapheme, 2);
        let mut clipboard = crate::clipboard::Clipboard::default();
        assert!(buf.selection_latch_key(kbmod::CTRL | vk::C) == Some(kbmod::CTRL | vk::C));
        buf.copy(&mut clipboard);
        assert_eq!(clipboard.read(), b"ab");
        assert!(buf.is_selection_latched());
        assert!(buf.selection_latch_key(kbmod::CTRL | vk::S) == Some(kbmod::CTRL | vk::S));
        assert_eq!(buffer_contents(&mut buf), "abcdef");
        assert!(buf.is_selection_latched());
        assert!(buf.selection_latch_key(vk::F2) == Some(vk::F2));
        assert!(buf.is_selection_latched());
        assert_eq!(buf.extract_user_selection(false).unwrap(), b"ab");
    }

    #[test]
    fn selection_latch_finishes_on_edits_and_is_document_local() {
        let mut buf = ruby_buffer("abcdef");
        let other = ruby_buffer("other");
        buf.start_selection_latch();
        buf.selection_update_delta(CursorMovement::Grapheme, 2);
        assert!(!other.is_selection_latched());
        buf.write_canon(b"X");
        assert!(!buf.is_selection_latched());
        assert_eq!(buffer_contents(&mut buf), "Xcdef");
        buf.start_selection_latch();
        buf.selection_update_delta(CursorMovement::Grapheme, 1);
        buf.delete(CursorMovement::Grapheme, -1);
        assert!(!buf.is_selection_latched());
        assert_eq!(buffer_contents(&mut buf), "Xdef");
        buf.cursor_move_to_logical(Point::default());
        buf.start_selection_latch();
        buf.delete(CursorMovement::Grapheme, -1);
        assert!(!buf.is_selection_latched());
    }

    #[test]
    fn ruby_render_preserves_source_and_colors_only_the_base() {
        let source = "前｜漢字《かんじ》後";
        let mut buf = ruby_buffer(source);
        let mut fb = Framebuffer::new();
        fb.flip(Size { width: 80, height: 6 });
        buf.render(
            Point::default(),
            Rect { left: 0, top: 0, right: 80, bottom: 6 },
            false,
            &mut fb,
        );
        let scratch = scratch_arena(None);
        let rendered = fb.render(&scratch);
        assert!(rendered.contains("漢字"), "{rendered:?}");
        assert!(!rendered.contains('｜'));
        assert!(!rendered.contains('《'));
        assert!(!rendered.contains("かんじ"));
        assert_eq!(buffer_contents(&mut buf), source);
        buf.select_all();
        assert_eq!(buf.extract_user_selection(false).unwrap(), source.as_bytes());
    }

    #[test]
    fn ruby_navigation_skips_markup_and_reports_the_reading() {
        let mut buf = ruby_buffer("前｜漢字《かんじ》後");
        assert_eq!(buf.ruby_reading_at_cursor(), None);
        buf.cursor_move_delta(CursorMovement::Grapheme, 1);
        assert_eq!(buf.cursor.offset, "前｜".len());
        assert_eq!(buf.ruby_reading_at_cursor().as_deref(), Some("かんじ"));
        assert_eq!(buf.cursor_visual_pos(), Point { x: 2, y: 0 });
        buf.cursor_move_delta(CursorMovement::Grapheme, 1);
        assert_eq!(buf.cursor.offset, "前｜漢".len());
        buf.cursor_move_delta(CursorMovement::Grapheme, 1);
        assert_eq!(buf.cursor.offset, "前｜漢字《かんじ》".len());
        assert_eq!(buf.ruby_reading_at_cursor(), None);
        assert_eq!(buf.cursor_visual_pos(), Point { x: 6, y: 0 });
        buf.cursor_move_delta(CursorMovement::Grapheme, -1);
        assert_eq!(buf.cursor.offset, "前｜漢".len());
        assert_eq!(buf.ruby_reading_at_cursor().as_deref(), Some("かんじ"));
        buf.cursor_move_to_visual(Point { x: 2, y: 0 });
        assert_eq!(buf.cursor.offset, "前｜".len());
    }

    #[test]
    fn format_editing_reveals_only_the_current_line_and_edits_markup() {
        let source = "｜前《まえ》\n｜母字《るび》《《圏点》》\n｜後《あと》";
        let mut buf = ruby_buffer(source);
        buf.cursor_move_to_logical(Point { x: 2, y: 1 });
        assert!(buf.toggle_format_editing());
        assert!(buf.is_format_editing());
        let mut fb = Framebuffer::new();
        fb.flip(Size { width: 80, height: 6 });
        buf.render(Point::default(), Rect { left: 0, top: 0, right: 80, bottom: 6 }, true, &mut fb);
        let scratch = scratch_arena(None);
        let rendered = fb.render(&scratch);
        for text in ["｜", "母字", "《るび》《《", "圏点", "》》"] {
            assert!(rendered.contains(text), "{rendered:?}");
        }
        assert!(!rendered.contains("まえ"), "{rendered:?}");
        assert!(!rendered.contains("あと"), "{rendered:?}");

        buf.cursor_move_to_offset("｜前《まえ》\n｜母字《る".len());
        buf.write_canon("ー".as_bytes());
        assert!(buffer_contents(&mut buf).contains("《るーび》"));
        buf.undo();
        assert_eq!(buffer_contents(&mut buf), source);
        buf.redo();
        assert!(buffer_contents(&mut buf).contains("《るーび》"));
        assert!(buf.toggle_format_editing());
        assert!(!buf.is_format_editing());
        assert!(buf.cursor.offset >= "｜前《まえ》\n｜母字《るーび》".len());
        assert_eq!(buf.cursor.logical_pos.y, 1);
    }

    #[test]
    fn format_editing_constrains_navigation_selection_and_structural_edits() {
        let source = "前の行\n《《母字》》\n後の行";
        let mut buf = ruby_buffer(source);
        buf.cursor_move_to_logical(Point { x: 2, y: 1 });
        assert!(buf.toggle_format_editing());
        let start = "前の行\n".len();
        let end = "前の行\n《《母字》》".len();
        buf.undo();
        assert_eq!(buffer_contents(&mut buf), source);
        buf.cursor_move_to_offset(0);
        assert_eq!(buf.cursor.offset, start);
        buf.cursor_move_delta(CursorMovement::Grapheme, -10);
        assert_eq!(buf.cursor.offset, start);
        buf.cursor_move_to_logical(Point::MAX);
        assert_eq!(buf.cursor.offset, end);
        buf.cursor_move_to_visual(Point::MAX);
        assert_eq!(buf.cursor.offset, end);
        buf.cursor_move_delta(CursorMovement::Word, 10);
        assert_eq!(buf.cursor.offset, end);
        buf.delete(CursorMovement::Grapheme, 1);
        buf.cursor_move_to_offset(start);
        buf.delete(CursorMovement::Word, -1);
        buf.write_canon(b"\n");
        buf.write_raw(b"a\nb");
        buf.move_selected_lines(super::MoveLineDirection::Down);
        buf.normalize_newlines(true);
        assert_eq!(buffer_contents(&mut buf), source);

        buf.selection_update_offset(0);
        buf.selection_update_logical(Point::MAX);
        let (beg, finish) = buf.selection_range().unwrap();
        assert_eq!((beg.offset, finish.offset), (start, end));
        buf.select_all();
        assert_eq!(buf.extract_user_selection(false).unwrap(), "《《母字》》".as_bytes());
        buf.write_canon("《《編集》》".as_bytes());
        assert_eq!(buffer_contents(&mut buf), "前の行\n《《編集》》\n後の行");
        buf.undo();
        buf.undo();
        assert_eq!(buffer_contents(&mut buf), source);
        assert_eq!(buf.cursor.logical_pos.y, 1);
        buf.redo();
        assert_eq!(buffer_contents(&mut buf), "前の行\n《《編集》》\n後の行");
        assert_eq!(buf.cursor.logical_pos.y, 1);
    }

    #[test]
    fn format_editing_search_and_replacement_stay_on_the_current_line() {
        let source = "母字\n｜母字《るび》《《母字》》\n母字";
        let mut buf = ruby_buffer(source);
        assert!(!buf.toggle_format_editing());
        buf.cursor_move_to_offset("母字\n｜".len());
        assert!(buf.toggle_format_editing());
        buf.find_and_select("母字", SearchOptions::default()).unwrap();
        assert_eq!(buf.cursor.logical_pos.y, 1);
        assert!(buf.find_and_replace_all("母字", SearchOptions::default(), b"a\nb").is_err());
        assert_eq!(buffer_contents(&mut buf), source);
        buf.find_and_replace_all("母字", SearchOptions::default(), "本文".as_bytes()).unwrap();
        assert_eq!(buffer_contents(&mut buf), "母字\n｜本文《るび》《《本文》》\n母字");
        assert_eq!(buf.cursor.logical_pos.y, 1);
        buf.find_and_select("存在しない", SearchOptions::default()).unwrap();
        assert_eq!(buf.cursor.logical_pos.y, 1);
        buf.undo();
        assert_eq!(buffer_contents(&mut buf), source);
        buf.toggle_format_editing();
        buf.cursor_move_to_offset(0);
        assert_eq!(buf.cursor.offset, 0);
    }

    #[test]
    fn format_editing_restores_wrap_boundaries_after_deleting_the_line_and_undo() {
        let source = "前\n｜母字《るび》あいうえお\n後";
        let mut buf = ruby_buffer(source);
        buf.set_wrap_chars(Some(2));
        buf.set_word_wrap(true);
        buf.set_width(80);
        buf.cursor_move_to_offset("前\n｜".len());
        assert!(buf.toggle_format_editing());
        let wraps = buf.format_edit.as_ref().unwrap().wraps.clone();
        assert!(!wraps.is_empty());
        buf.select_all();
        buf.delete(CursorMovement::Grapheme, 1);
        assert_eq!(buffer_contents(&mut buf), "前\n\n後");
        assert_eq!(buf.cursor.logical_pos.y, 1);
        buf.undo();
        assert_eq!(buffer_contents(&mut buf), source);
        assert_eq!(buf.format_edit.as_ref().unwrap().wraps, wraps);
        buf.redo();
        assert_eq!(buffer_contents(&mut buf), "前\n\n後");
        assert_eq!(buf.cursor.logical_pos.y, 1);
        buf.toggle_format_editing();
        assert!(!buf.is_format_editing());
    }

    #[test]
    fn format_editing_keeps_opening_markup_and_insertions_on_the_wrapped_row() {
        let mut buf = ruby_buffer("前\nあい｜母字《るび》うえ\n後");
        buf.set_wrap_chars(Some(2));
        buf.set_word_wrap(true);
        buf.set_width(80);
        buf.cursor_move_to_offset("前\nあい｜".len());
        assert!(buf.toggle_format_editing());
        let row = buf.cursor_move_to_visual_internal(buf.cursor, Point { x: 0, y: 2 });
        assert_eq!(row.offset, "前\nあい".len());
        buf.cursor_move_to_visual(Point { x: 0, y: 2 });
        buf.write_canon(b"A");
        assert_eq!(buf.cursor.visual_pos, Point { x: 1, y: 2 });
        assert_eq!(buffer_contents(&mut buf), "前\nあいA｜母字《るび》うえ\n後");
        buf.undo();
        assert_eq!(buffer_contents(&mut buf), "前\nあい｜母字《るび》うえ\n後");
    }

    #[test]
    fn format_editing_preserves_wraps_and_other_lines() {
        let source = "先頭\nあ｜母字《るび》いう《《圏点》》えお\n最後";
        let mut buf = ruby_buffer(source);
        buf.set_wrap_chars(Some(3));
        buf.set_word_wrap(true);
        buf.set_width(80);
        buf.cursor_move_to_offset("先頭\nあ｜".len());
        let last = buf.cursor_move_to_logical_internal(buf.cursor, Point { x: 0, y: 2 });
        let old_rows = buf.stats.visual_lines;
        let mut old_wraps = Vec::new();
        for y in 2..last.visual_pos.y {
            old_wraps
                .push(buf.cursor_move_to_visual_internal(buf.cursor, Point { x: 0, y }).offset);
        }
        assert!(buf.toggle_format_editing());
        assert_eq!(buf.stats.visual_lines, old_rows);
        for (i, offset) in old_wraps.iter().enumerate() {
            let row =
                buf.cursor_move_to_visual_internal(buf.cursor, Point { x: 0, y: i as isize + 2 });
            assert_eq!(row.offset, *offset);
        }
        let current_last = buf.cursor_move_to_logical_internal(buf.cursor, Point { x: 0, y: 2 });
        assert_eq!(current_last.visual_pos, last.visual_pos);
        buf.write_canon(b"extra");
        assert_eq!(buf.stats.visual_lines, old_rows);
        buf.undo();
        assert_eq!(buffer_contents(&mut buf), source);
        buf.toggle_format_editing();
        assert_eq!(buf.stats.visual_lines, old_rows);
    }

    #[test]
    fn ruby_insertion_uses_source_boundaries_at_each_visible_position() {
        for prefix in ["", "前"] {
            let source = format!("{prefix}｜母字《るび》後");
            for (position, expected) in [
                (0, format!("{prefix}A｜母字《るび》後")),
                (1, format!("{prefix}｜母A字《るび》後")),
                (2, format!("{prefix}｜母字《るび》A後")),
            ] {
                for visual in [false, true] {
                    for raw in [false, true] {
                        let mut buf = ruby_buffer(&source);
                        if visual {
                            buf.cursor_move_to_visual(Point {
                                x: (prefix.chars().count() as isize + position) * 2,
                                y: 0,
                            });
                        } else {
                            buf.cursor_move_delta(
                                CursorMovement::Grapheme,
                                prefix.chars().count() as isize + position,
                            );
                        }
                        if raw {
                            buf.write_raw(b"A");
                        } else {
                            buf.write_canon(b"A");
                        }
                        assert_eq!(buffer_contents(&mut buf), expected);
                        buf.undo();
                        assert_eq!(buffer_contents(&mut buf), source);
                        buf.redo();
                        assert_eq!(buffer_contents(&mut buf), expected);
                    }
                }
            }
        }
    }

    #[test]
    fn emphasis_insertion_uses_source_boundaries_at_each_visible_position() {
        for prefix in ["", "前"] {
            let source = format!("{prefix}《《母字》》後");
            for (position, expected) in [
                (0, format!("{prefix}A《《母字》》後")),
                (1, format!("{prefix}《《母A字》》後")),
                (2, format!("{prefix}《《母字》》A後")),
            ] {
                for visual in [false, true] {
                    for raw in [false, true] {
                        let mut buf = ruby_buffer(&source);
                        if visual {
                            buf.cursor_move_to_visual(Point {
                                x: (prefix.chars().count() as isize + position) * 2,
                                y: 0,
                            });
                        } else {
                            buf.cursor_move_delta(
                                CursorMovement::Grapheme,
                                prefix.chars().count() as isize + position,
                            );
                        }
                        if raw {
                            buf.write_raw(b"A");
                        } else {
                            buf.write_canon(b"A");
                        }
                        assert_eq!(buffer_contents(&mut buf), expected);
                        buf.undo();
                        assert_eq!(buffer_contents(&mut buf), source);
                        buf.redo();
                        assert_eq!(buffer_contents(&mut buf), expected);
                    }
                }
            }
        }
    }

    #[test]
    fn emphasis_boundary_insertion_keeps_successive_input_outside_markup() {
        let mut buf = ruby_buffer("《《母字》》");
        buf.write_canon(b"A");
        buf.write_canon(b"B");
        assert_eq!(buffer_contents(&mut buf), "AB《《母字》》");

        for next in ["《《圏点》》", "｜漢字《かんじ》"] {
            let mut buf = ruby_buffer(&format!("《《母字》》{next}"));
            buf.cursor_move_delta(CursorMovement::Grapheme, 2);
            buf.write_canon(b"A");
            assert_eq!(buffer_contents(&mut buf), format!("《《母字》》A{next}"));
        }

        let mut buf = ruby_buffer("《《母字》》");
        buf.set_ruby_display(false);
        buf.cursor_move_to_offset("《《".len());
        buf.write_canon(b"A");
        assert_eq!(buffer_contents(&mut buf), "《《A母字》》");
    }

    #[test]
    fn ruby_boundary_insertion_keeps_successive_input_outside_markup() {
        let mut buf = ruby_buffer("｜母字《るび》");
        buf.write_canon(b"A");
        buf.write_canon(b"B");
        assert_eq!(buffer_contents(&mut buf), "AB｜母字《るび》");

        let mut buf = ruby_buffer("｜母字《るび》｜漢字《かんじ》");
        buf.cursor_move_delta(CursorMovement::Grapheme, 2);
        buf.write_canon(b"A");
        assert_eq!(buffer_contents(&mut buf), "｜母字《るび》A｜漢字《かんじ》");

        let mut buf = ruby_buffer("｜母字《るび》");
        buf.set_ruby_display(false);
        buf.cursor_move_to_offset("｜".len());
        buf.write_canon(b"A");
        assert_eq!(buffer_contents(&mut buf), "｜A母字《るび》");
    }

    #[test]
    fn ruby_wrap_uses_visible_width_and_incomplete_markup_stays_literal() {
        let mut buf = ruby_buffer("あ｜漢字《ながいよみがな》いう\n｜未完《よみ");
        buf.set_wrap_chars(Some(2));
        buf.set_word_wrap(true);
        buf.set_width(80);
        buf.cursor_move_to_offset("あ｜漢字《ながいよみがな》い".len());
        assert_eq!(buf.cursor_visual_pos(), Point { x: 4, y: 1 });
        buf.cursor_move_to_offset("あ｜漢字《ながいよみがな》いう\n｜".len());
        assert_eq!(buf.cursor_visual_pos(), Point { x: 2, y: 3 });
        assert_eq!(buf.ruby_reading_at_cursor(), None);
    }

    #[test]
    fn ruby_cache_updates_when_markup_is_completed_and_undone() {
        let mut buf = ruby_buffer("｜漢字《かんじ");
        buf.cursor_move_to_logical(Point::MAX);
        buf.write_raw("》".as_bytes());
        assert_eq!(buf.cursor_visual_pos(), Point { x: 4, y: 0 });
        buf.undo();
        assert_eq!(buf.cursor_visual_pos().x, 14);
        buf.redo();
        assert_eq!(buf.cursor_visual_pos(), Point { x: 4, y: 0 });
        buf.cursor_move_to_logical(Point::default());
        assert_eq!(buf.ruby_reading_at_cursor().as_deref(), Some("かんじ"));
    }

    #[test]
    fn ruby_partial_deletion_keeps_the_reading_and_undo_restores_source() {
        let source = "前｜漢字《かんじ》後";
        let mut buf = ruby_buffer(source);
        buf.cursor_move_to_visual(Point { x: 6, y: 0 });
        buf.delete(CursorMovement::Grapheme, -1);
        assert_eq!(buffer_contents(&mut buf), "前｜漢《かんじ》後");
        buf.undo();
        assert_eq!(buffer_contents(&mut buf), source);
        buf.cursor_move_to_visual(Point { x: 2, y: 0 });
        buf.delete(CursorMovement::Grapheme, 1);
        assert_eq!(buffer_contents(&mut buf), "前｜字《かんじ》後");

        let mut buf = ruby_buffer("｜漢《かん》語");
        buf.delete(CursorMovement::Grapheme, -1);
        assert_eq!(buffer_contents(&mut buf), "｜漢《かん》語");
        buf.delete(CursorMovement::Grapheme, 1);
        assert_eq!(buffer_contents(&mut buf), "語");
    }

    #[test]
    fn ruby_selection_copies_complete_markup_and_can_be_replaced() {
        let source = "前｜漢字《かんじ》後";
        let mut buf = ruby_buffer(source);
        buf.cursor_move_to_visual(Point { x: 2, y: 0 });
        buf.start_selection();
        buf.selection_update_delta(CursorMovement::Grapheme, 2);
        assert_eq!(buf.extract_user_selection(false).unwrap(), "｜漢字《かんじ》".as_bytes());
        buf.write_canon("語".as_bytes());
        assert_eq!(buffer_contents(&mut buf), "前語後");
        buf.undo();
        assert_eq!(buffer_contents(&mut buf), source);
    }

    #[test]
    fn emphasis_and_ruby_share_visible_layout_and_switch_messages() {
        let source = "前《《圏点》》｜漢字《かんじ》後";
        let mut buf = ruby_buffer(source);
        buf.set_wrap_chars(Some(2));
        buf.set_word_wrap(true);
        buf.set_width(80);
        assert_eq!(buf.annotation_at_cursor(), None);
        buf.cursor_move_delta(CursorMovement::Grapheme, 1);
        assert_eq!(buf.annotation_at_cursor().as_deref(), Some("圏点:[﹅]"));
        assert_eq!(buf.cursor.offset, "前《《".len());
        buf.cursor_move_delta(CursorMovement::Grapheme, 2);
        assert_eq!(buf.annotation_at_cursor().as_deref(), Some("ルビ:[かんじ]"));
        assert_eq!(buf.cursor_visual_pos(), Point { x: 2, y: 1 });
        buf.cursor_move_delta(CursorMovement::Grapheme, -1);
        assert_eq!(buf.annotation_at_cursor().as_deref(), Some("圏点:[﹅]"));

        let mut fb = Framebuffer::new();
        fb.flip(Size { width: 80, height: 6 });
        buf.render(
            Point::default(),
            Rect { left: 0, top: 0, right: 80, bottom: 6 },
            false,
            &mut fb,
        );
        let scratch = scratch_arena(None);
        let rendered = fb.render(&scratch);
        assert!(rendered.contains("前"));
        assert!(rendered.contains("圏"));
        assert!(rendered.contains("点漢"));
        assert!(!rendered.contains('《'));
        assert!(!rendered.contains('》'));
        assert!(!rendered.contains('｜'));
        assert!(!rendered.contains("かんじ"));
        assert_eq!(buffer_contents(&mut buf), source);
    }

    #[test]
    fn emphasis_selection_and_deletion_preserve_source_markup() {
        let source = "前《《圏点》》後";
        let mut buf = ruby_buffer(source);
        buf.cursor_move_to_visual(Point { x: 6, y: 0 });
        assert_eq!(buf.annotation_at_cursor(), None);
        buf.delete(CursorMovement::Grapheme, -1);
        assert_eq!(buffer_contents(&mut buf), "前《《圏》》後");
        buf.undo();
        assert_eq!(buffer_contents(&mut buf), source);
        buf.cursor_move_to_visual(Point { x: 2, y: 0 });
        buf.start_selection();
        buf.selection_update_delta(CursorMovement::Grapheme, 2);
        assert_eq!(buf.extract_user_selection(false).unwrap(), "《《圏点》》".as_bytes());
        buf.write_canon("強調".as_bytes());
        assert_eq!(buffer_contents(&mut buf), "前強調後");
        buf.undo();
        assert_eq!(buffer_contents(&mut buf), source);
    }

    #[test]
    fn emphasis_completion_and_undo_recalculate_hidden_brackets() {
        let mut buf = ruby_buffer("《《圏点》");
        buf.cursor_move_to_logical(Point::MAX);
        assert_eq!(buf.cursor_visual_pos().x, 10);
        assert_eq!(buf.annotation_at_cursor(), None);
        buf.write_raw("》".as_bytes());
        assert_eq!(buf.cursor_visual_pos().x, 4);
        buf.undo();
        assert_eq!(buf.cursor_visual_pos().x, 10);
        buf.redo();
        assert_eq!(buf.cursor_visual_pos().x, 4);
        buf.cursor_move_to_logical(Point::default());
        assert_eq!(buf.annotation_at_cursor().as_deref(), Some("圏点:[﹅]"));
    }

    #[test]
    fn fixed_japanese_wrap_width_and_resize() {
        let mut buf = TextBuffer::new(false).unwrap();
        buf.set_crlf(false);
        buf.write_raw("あいう、え\nかきくけこ".as_bytes());
        buf.set_wrap_chars(Some(3));
        buf.set_word_wrap(true);
        buf.set_width(100);

        // Fixed wrapping leaves punctuation in place for later warning display.
        buf.cursor_move_to_logical(Point { x: 2, y: 0 });
        assert_eq!(buf.cursor_visual_pos(), Point { x: 4, y: 0 });
        buf.cursor_move_to_logical(Point { x: 4, y: 0 });
        assert_eq!(buf.cursor_visual_pos(), Point { x: 2, y: 1 });

        buf.cursor_move_to_logical(Point { x: 5, y: 0 });
        buf.set_width(4);
        assert_eq!(buf.cursor_visual_pos(), Point { x: 2, y: 2 });
        buf.set_width(100);
        assert_eq!(buf.cursor_visual_pos(), Point { x: 4, y: 1 });

        buf.set_word_wrap(false);
        buf.set_width(100);
        assert_eq!(buf.cursor_visual_pos(), Point { x: 10, y: 0 });
        buf.set_word_wrap(true);
        buf.set_width(100);
        assert_eq!(buf.cursor_visual_pos(), Point { x: 4, y: 1 });
        assert_eq!(buffer_contents(&mut buf), "あいう、え\nかきくけこ");
    }

    #[test]
    fn fixed_japanese_wrap_counts_half_width_and_combining_characters() {
        let mut buf = TextBuffer::new(false).unwrap();
        buf.write_raw("あabか\u{3099}いう".as_bytes());
        buf.set_wrap_chars(Some(3));
        buf.set_word_wrap(true);
        buf.set_width(100);
        buf.cursor_move_to_logical(Point { x: 5, y: 0 });
        assert_eq!(buf.cursor_visual_pos(), Point { x: 2, y: 1 });
        assert_eq!(buf.cursor_logical_pos(), Point { x: 5, y: 0 });
    }

    #[test]
    fn replace_one_zero_width() {
        let mut buf = TextBuffer::new(false).unwrap();
        buf.set_crlf(false);
        buf.set_insert_final_newline(true);
        buf.write_raw(b"a\nb\n");
        buf.cursor_move_to_logical(Default::default());

        for _ in 0..6 {
            buf.find_and_replace(
                "$",
                SearchOptions { use_regex: true, ..Default::default() },
                b"x",
            )
            .unwrap();
        }

        assert_eq!(buffer_contents(&mut buf), "axx\nbxx\nx\n");
    }

    #[test]
    fn replace_all_zero_width() {
        let mut buf = TextBuffer::new(false).unwrap();
        buf.set_crlf(false);
        buf.set_insert_final_newline(true);
        buf.write_raw(b"a\nb\n");

        buf.find_and_replace_all(
            "$",
            SearchOptions { use_regex: true, ..Default::default() },
            b"x",
        )
        .unwrap();

        assert_eq!(buffer_contents(&mut buf), "ax\nbx\nx\n");
    }
}
