// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Warning rules operate on displayed graphemes, without modifying line breaks.

use std::collections::BTreeMap;
use std::ops::Range;
use std::rc::Rc;

use crate::helpers::{CoordType, Point};
use crate::unicode::MeasurementConfig;

#[derive(Clone, Debug, Default)]
pub struct ForbiddenRules {
    pub line_start: String,
    pub line_end: String,
    pub paragraph_start_allowed: String,
    pub inseparable: Vec<String>,
}

impl ForbiddenRules {
    pub fn validate(&self) -> Result<(), &'static str> {
        fn printable(text: &str) -> bool {
            text.chars().all(|ch| {
                !ch.is_control()
                    && !matches!(ch, '\u{2028}' | '\u{2029}' | '\u{200b}'..='\u{200f}'
                    | '\u{202a}'..='\u{202e}' | '\u{2060}'..='\u{206f}' | '\u{feff}')
            })
        }
        for (text, field) in [
            (&self.line_start, "forbidden.line_start"),
            (&self.line_end, "forbidden.line_end"),
            (&self.paragraph_start_allowed, "forbidden.paragraph_start_allowed"),
        ] {
            if !printable(text) {
                return Err(field);
            }
        }
        for sequence in &self.inseparable {
            let bytes = sequence.as_bytes();
            if !printable(sequence)
                || MeasurementConfig::new(&bytes).goto_offset(usize::MAX).logical_pos.x < 2
            {
                return Err(
                    "forbidden.inseparable: each entry must contain at least two display characters",
                );
            }
        }
        Ok(())
    }
}

pub(super) struct Cell {
    pub source: Range<usize>,
    pub text: String,
    pub pos: Point,
    pub width: CoordType,
}

#[derive(Clone, Debug)]
pub(super) struct Warning {
    pub source: Range<usize>,
    pub pos: Point,
    pub width: CoordType,
    pub reasons: Vec<String>,
}

#[derive(Default)]
pub(super) struct WarningCache {
    pub key: Option<(u32, CoordType, bool)>,
    pub lines: BTreeMap<usize, Rc<Vec<Warning>>>,
}

pub(super) fn warnings(
    cells: &[Cell],
    rules: &ForbiddenRules,
    ruby_bases: &[Range<usize>],
) -> Vec<Warning> {
    let mut marked: BTreeMap<usize, Vec<String>> = BTreeMap::new();
    let mut mark = |range: Range<usize>, message: String| {
        for index in range {
            let reasons = marked.entry(index).or_default();
            if !reasons.contains(&message) {
                reasons.push(message.clone());
            }
        }
    };
    for (index, cell) in cells.iter().enumerate() {
        let head = index == 0 || cells[index - 1].pos.y != cell.pos.y;
        let tail = index + 1 == cells.len() || cells[index + 1].pos.y != cell.pos.y;
        let ch = cell.text.chars().next().unwrap_or('\0');
        if head
            && rules.line_start.contains(ch)
            && !(index == 0 && rules.paragraph_start_allowed.contains(ch))
        {
            mark(index..index + 1, format!("警告: 行頭禁則（「{ch}」）"));
        }
        if tail && rules.line_end.contains(ch) {
            mark(index..index + 1, format!("警告: 行末禁則（「{ch}」）"));
        }
    }

    let mut text = String::new();
    let mut offsets = Vec::with_capacity(cells.len() + 1);
    for cell in cells {
        offsets.push(text.len());
        text.push_str(&cell.text);
    }
    offsets.push(text.len());
    for sequence in &rules.inseparable {
        if sequence.is_empty() {
            continue;
        }
        for start in 0..cells.len() {
            let from = offsets[start];
            if !text[from..].starts_with(sequence) {
                continue;
            }
            let Ok(end) = offsets.binary_search(&(from + sequence.len())) else {
                continue;
            };
            if end > start && cells[start].pos.y != cells[end - 1].pos.y {
                mark(
                    start..end,
                    format!("警告: 分離禁止文字列「{sequence}」が行の境界で分離しています"),
                );
            }
        }
    }
    for base in ruby_bases {
        let start = cells.partition_point(|cell| cell.source.end <= base.start);
        let end = cells.partition_point(|cell| cell.source.start < base.end);
        if end > start && cells[start].pos.y != cells[end - 1].pos.y {
            mark(start..end, "警告: ルビの母字が行の境界で分離しています".to_string());
        }
    }
    marked
        .into_iter()
        .map(|(index, reasons)| Warning {
            source: cells[index].source.clone(),
            pos: cells[index].pos,
            width: cells[index].width,
            reasons,
        })
        .collect()
}
