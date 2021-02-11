use regex::Regex;

pub fn reg(s: &str) -> Regex {
    Regex::new(s).unwrap()
}
