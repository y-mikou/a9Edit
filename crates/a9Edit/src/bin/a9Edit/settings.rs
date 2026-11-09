use std::path::PathBuf;
use std::rc::Rc;

use a9edit::buffer::{ForbiddenRules, TextBuffer};
use a9edit::cell::{Ref, SemiRefCell};
use a9edit::json;
use a9edit::lsh::{LANGUAGES, Language};
use stdext::arena::{read_to_string, scratch_arena};
use stdext::arena_format;

use crate::apperr;

pub struct Settings {
    pub path: PathBuf,
    pub file_associations: Vec<(String, &'static Language)>,
    pub forbidden: Option<Rc<ForbiddenRules>>,
}

struct SettingsCell(SemiRefCell<Settings>);
unsafe impl Sync for SettingsCell {}
static SETTINGS: SettingsCell = SettingsCell(SemiRefCell::new(Settings::new()));

impl Settings {
    /// Fills the given settings.json text buffer with some initial contents for convenience.
    pub fn bootstrap(tb: &mut TextBuffer) {
        tb.set_crlf(false);
        tb.write_raw(include_bytes!("../../../../../settings.example.json"));
        tb.cursor_move_to_logical(Default::default());
        tb.mark_as_clean();
    }

    const fn new() -> Self {
        Settings { path: PathBuf::new(), file_associations: Vec::new(), forbidden: None }
    }

    pub fn borrow() -> Ref<'static, Settings> {
        SETTINGS.0.borrow()
    }

    pub fn reload() -> apperr::Result<()> {
        let s = &mut *SETTINGS.0.borrow_mut();

        // Reset all members if we had been loaded previously.
        if !s.path.as_os_str().is_empty() {
            *s = Settings::new();
        }

        s.load()
    }

    fn load(&mut self) -> apperr::Result<()> {
        self.path = match settings_json_path() {
            Some(p) => p,
            None => return Ok(()),
        };

        let scratch = scratch_arena(None);
        let str = match read_to_string(&scratch, &self.path) {
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => return Ok(()),
            Err(err) => return Err(err.into()),
            Ok(str) => str,
        };
        let Ok(json) = json::parse(&scratch, &str) else {
            return Err(apperr::Error::SettingsInvalid("Invalid JSON"));
        };
        let Some(root) = json.as_object() else {
            return Err(apperr::Error::SettingsInvalid("Non-object root"));
        };

        if let Some(f) = root.get_object("files.associations") {
            for &(mut key, ref value) in f.iter() {
                if !key.contains('/') {
                    key = arena_format!(&*scratch, "**/{key}").leak();
                }

                let Some(id) = value.as_str() else {
                    return Err(apperr::Error::SettingsInvalid("files.associations"));
                };
                let Some(language) = LANGUAGES.iter().find(|lang| lang.id == id) else {
                    return Err(apperr::Error::SettingsInvalid("language ID"));
                };

                self.file_associations.push((key.to_string(), language));
            }
        }

        if let Some(value) = root.get("forbidden") {
            self.forbidden = Some(Rc::new(parse_forbidden(value)?));
        }

        Ok(())
    }
}

fn parse_forbidden(value: &json::Value<'_>) -> apperr::Result<ForbiddenRules> {
    let object =
        value.as_object().ok_or(apperr::Error::SettingsInvalid("forbidden: expected an object"))?;
    let mut rules = ForbiddenRules::default();
    for (key, target, error) in [
        ("line_start", &mut rules.line_start, "forbidden.line_start: expected a string"),
        ("line_end", &mut rules.line_end, "forbidden.line_end: expected a string"),
        (
            "paragraph_start_allowed",
            &mut rules.paragraph_start_allowed,
            "forbidden.paragraph_start_allowed: expected a string",
        ),
    ] {
        if let Some(value) = object.get(key) {
            *target = value.as_str().ok_or(apperr::Error::SettingsInvalid(error))?.to_string();
        }
    }
    if let Some(value) = object.get("inseparable") {
        let array = value.as_array().ok_or(apperr::Error::SettingsInvalid(
            "forbidden.inseparable: expected an array of strings",
        ))?;
        for value in array {
            rules.inseparable.push(
                value
                    .as_str()
                    .ok_or(apperr::Error::SettingsInvalid(
                        "forbidden.inseparable: expected an array of strings",
                    ))?
                    .to_string(),
            );
        }
    }
    if object.iter().any(|(key, _)| {
        !["line_start", "line_end", "paragraph_start_allowed", "inseparable"].contains(key)
    }) {
        return Err(apperr::Error::SettingsInvalid("forbidden: unknown key"));
    }
    rules.validate().map_err(apperr::Error::SettingsInvalid)?;
    Ok(rules)
}

fn settings_json_path() -> Option<PathBuf> {
    let mut config_dir = config_dir()?;
    config_dir.push("settings.json");
    Some(config_dir)
}

fn config_dir() -> Option<PathBuf> {
    fn var_path(key: &str) -> Option<PathBuf> {
        std::env::var_os(key).map(PathBuf::from)
    }

    fn push(mut path: PathBuf, suffix: &str) -> PathBuf {
        path.push(suffix);
        path
    }

    #[cfg(target_os = "windows")]
    {
        var_path("APPDATA").map(|p| push(p, "a9Edit"))
    }
    #[cfg(any(target_os = "macos", target_os = "ios"))]
    {
        var_path("HOME").map(|p| push(p, "Library/Application Support/a9Edit"))
    }
    #[cfg(not(any(target_os = "windows", target_os = "macos", target_os = "ios")))]
    {
        var_path("XDG_CONFIG_HOME")
            .or_else(|| var_path("HOME").map(|p| push(p, ".config")))
            .map(|p| push(p, "a9Edit"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rules(text: &str) -> apperr::Result<ForbiddenRules> {
        let scratch = scratch_arena(None);
        let value = json::parse(&scratch, text).unwrap();
        parse_forbidden(&value)
    }

    #[test]
    fn forbidden_settings_read_strings_and_sequences() {
        let parsed = rules(r#"{"line_start":"。、", "line_end":"（", "paragraph_start_allowed":"（", "inseparable":["……", "――"]}"#).unwrap();
        assert_eq!(parsed.line_start, "。、");
        assert_eq!(parsed.line_end, "（");
        assert_eq!(parsed.paragraph_start_allowed, "（");
        assert_eq!(parsed.inseparable, ["……", "――"]);
        assert!(rules("{}").is_ok());
        let scratch = scratch_arena(None);
        let example =
            json::parse(&scratch, include_str!("../../../../../settings.example.json")).unwrap();
        let example =
            parse_forbidden(example.as_object().unwrap().get("forbidden").unwrap()).unwrap();
        assert!(example.line_start.contains('、'));
        assert!(example.line_end.contains('（'));
        assert!(example.paragraph_start_allowed.contains('「'));
    }

    #[test]
    fn forbidden_settings_reject_wrong_types_and_invalid_sequences() {
        for text in [
            "null",
            "[]",
            r#"{"line_start": 1}"#,
            r#"{"line_end": []}"#,
            r#"{"paragraph_start_allowed": false}"#,
            r#"{"inseparable": "……"}"#,
            r#"{"inseparable": [1]}"#,
            r#"{"inseparable": [""]}"#,
            r#"{"inseparable": ["あ"]}"#,
            r#"{"inseparable": ["か\u3099"]}"#,
            r#"{"line_start":"\n"}"#,
            r#"{"inseparable":["a\nb"]}"#,
            r#"{"line_strat":"、"}"#,
        ] {
            assert!(rules(text).is_err(), "{text}");
        }
    }
}
