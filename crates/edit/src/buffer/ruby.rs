// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Line-local ruby/emphasis metadata. Byte offsets refer to the unchanged source.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ops::Range;
use std::rc::Rc;

use crate::document::ReadableDocument;
use crate::unicode::HiddenText;

#[derive(Debug)]
pub(super) enum AnnotationKind {
    Ruby(String),
    Emphasis,
}

#[derive(Debug)]
pub(super) struct Ruby {
    pub markup: Range<usize>,
    pub base: Range<usize>,
    pub kind: AnnotationKind,
}

pub(super) struct Line {
    pub end: usize,
    pub ruby: Vec<Ruby>,
}

#[derive(Default)]
struct Cache {
    generation: Option<u32>,
    lines: BTreeMap<usize, Rc<Line>>,
}

#[derive(Default)]
pub(super) struct RubyCache(RefCell<Cache>);

impl RubyCache {
    pub fn prepare(&self, generation: u32) {
        let mut cache = self.0.borrow_mut();
        if cache.generation != Some(generation) {
            cache.lines.clear();
            cache.generation = Some(generation);
        }
    }

    pub fn line(&self, doc: &dyn ReadableDocument, offset: usize) -> Rc<Line> {
        let mut cache = self.0.borrow_mut();
        if let Some((_, line)) = cache.lines.range(..=offset).next_back()
            && offset < line.end
        {
            return line.clone();
        }

        let mut start = offset;
        loop {
            let chunk = doc.read_backward(start);
            if let Some(index) = chunk.iter().rposition(|&byte| byte == b'\n') {
                start -= chunk.len() - index - 1;
                break;
            }
            start -= chunk.len();
            if chunk.is_empty() {
                break;
            }
        }

        let mut bytes = Vec::new();
        let mut end = start;
        loop {
            let chunk = doc.read_forward(end);
            if let Some(index) = chunk.iter().position(|&byte| byte == b'\n') {
                bytes.extend_from_slice(&chunk[..index]);
                end += index + 1;
                break;
            }
            bytes.extend_from_slice(chunk);
            end += chunk.len();
            if chunk.is_empty() {
                // Include the end-of-document insertion point in the cache.
                end += 1;
                break;
            }
        }

        let line = Rc::new(Line { end, ruby: parse(&bytes, start) });
        cache.lines.insert(start, line.clone());
        line
    }
}

impl HiddenText for RubyCache {
    fn hidden_range(&self, doc: &dyn ReadableDocument, offset: usize) -> Option<Range<usize>> {
        let line = self.line(doc, offset);
        for ruby in &line.ruby {
            if (ruby.markup.start..ruby.base.start).contains(&offset) {
                return Some(ruby.markup.start..ruby.base.start);
            }
            if (ruby.base.end..ruby.markup.end).contains(&offset) {
                return Some(ruby.base.end..ruby.markup.end);
            }
        }
        None
    }
}

fn parse(bytes: &[u8], start: usize) -> Vec<Ruby> {
    let Ok(text) = std::str::from_utf8(bytes) else {
        return Vec::new();
    };
    let mut ruby = Vec::new();
    let mut offset = 0;
    while let Some(index) = text[offset..].find(['｜', '《']) {
        let markup_start = offset + index;
        if text[markup_start..].starts_with('《') {
            offset = markup_start + '《'.len_utf8();
            if !text[markup_start..].starts_with("《《") {
                continue;
            }
            let base_start = markup_start + "《《".len();
            offset = base_start;
            let Some((base_length, '》')) =
                text[base_start..].char_indices().find(|(_, ch)| matches!(ch, '《' | '》' | '\r'))
            else {
                continue;
            };
            let base_end = base_start + base_length;
            if base_length == 0 || !text[base_end..].starts_with("》》") {
                continue;
            }
            offset = base_end + "》》".len();
            ruby.push(Ruby {
                markup: start + markup_start..start + offset,
                base: start + base_start..start + base_end,
                kind: AnnotationKind::Emphasis,
            });
            continue;
        }
        let base_start = markup_start + '｜'.len_utf8();
        offset = base_start;
        let Some((base_length, '《')) = text[base_start..]
            .char_indices()
            .find(|(_, ch)| matches!(ch, '｜' | '《' | '》' | '\r'))
        else {
            continue;
        };
        if base_length == 0 {
            continue;
        }
        let base_end = base_start + base_length;
        let reading_start = base_end + '《'.len_utf8();
        let Some((reading_length, '》')) = text[reading_start..]
            .char_indices()
            .find(|(_, ch)| matches!(ch, '｜' | '《' | '》' | '\r'))
        else {
            continue;
        };
        if reading_length == 0 {
            continue;
        }
        let reading_end = reading_start + reading_length;
        offset = reading_end + '》'.len_utf8();
        ruby.push(Ruby {
            markup: start + markup_start..start + offset,
            base: start + base_start..start + base_end,
            kind: AnnotationKind::Ruby(text[reading_start..reading_end].to_string()),
        });
    }
    ruby
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_only_complete_ruby_and_keeps_source_offsets() {
        let text = "前｜漢字《かんじ》後｜空《》｜未完《よみ《《圏点》》";
        let ruby = parse(text.as_bytes(), 10);
        assert_eq!(ruby.len(), 2);
        assert_eq!(&text[ruby[0].base.start - 10..ruby[0].base.end - 10], "漢字");
        assert!(matches!(&ruby[0].kind, AnnotationKind::Ruby(reading) if reading == "かんじ"));
        assert!(matches!(ruby[1].kind, AnnotationKind::Emphasis));
        assert_eq!(&text[ruby[1].base.start - 10..ruby[1].base.end - 10], "圏点");
    }

    #[test]
    fn emphasis_requires_nonempty_base_and_complete_double_brackets() {
        for text in ["《《》》", "《《未完", "《《片側》", "《《改行\r》》", "《通常》"]
        {
            assert!(parse(text.as_bytes(), 0).is_empty(), "{text}");
        }
        let ruby = parse("《《a》》｜字《じ》《《b》》".as_bytes(), 0);
        assert_eq!(ruby.len(), 3);
        assert!(matches!(ruby[0].kind, AnnotationKind::Emphasis));
        assert!(matches!(ruby[1].kind, AnnotationKind::Ruby(_)));
        assert!(matches!(ruby[2].kind, AnnotationKind::Emphasis));
    }
}
