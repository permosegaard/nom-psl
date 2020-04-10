#[macro_use]
extern crate nom;

#[macro_use]
extern crate log;

use std::collections::HashMap;
use std::env;
use std::fs;
use std::io;
use std::path::PathBuf;

use cache_2q::Cache;

#[derive(Debug, PartialEq)]
pub enum DivisionSep {
    Begin,
    End,
}

#[derive(Debug, PartialEq)]
pub enum Division {
    ICANN(DivisionSep),
    PRIVATE(DivisionSep),
    Invalid,
}

#[derive(Debug, PartialEq)]
pub enum SuffixType {
    Exception,
    Wildcard,
    Normal,
}

#[derive(Debug, PartialEq)]
pub enum Rule {
    Division(Division),
    Comment(String),
    Suffix(Vec<String>, SuffixType),
}

named!( division_begin<&str, Division>,
    do_parse!(
        tag!("// ===BEGIN ") >>
        m: take_until!(" DOMAINS===") >>
        tag!(" DOMAINS===") >>
        (match m {
            "ICANN" => Division::ICANN(DivisionSep::Begin),
            "PRIVATE" => Division::PRIVATE(DivisionSep::Begin),
            _ => Division::Invalid,
        })
    )
);

named!( division_end<&str, Division>,
    do_parse!(
        tag!("// ===END ") >>
        m: take_until!(" DOMAINS===") >>
        tag!(" DOMAINS===") >>
        (match m {
            "ICANN" => Division::ICANN(DivisionSep::End),
            "PRIVATE" => Division::PRIVATE(DivisionSep::End),
            _ => Division::Invalid,
        })
    )
);

named!(division<&str, Rule>,
   do_parse!(
       division: alt!(
           division_begin
           |
           division_end
       ) >>
       tag!("\n") >>
       ( Rule::Division(division) )
   )
);

named!( comment<&str, Rule>,
    do_parse!(
        tag!("//") >>
        comment_text: take_until!("\n") >>
        tag!("\n") >>
        ( Rule::Comment(comment_text.to_string()) )
    )
);

named!( exception_rule<&str, Rule>,
    do_parse!(
        tag!("!") >>
        rule_text: take_till!(char::is_whitespace) >>
        tag!("\n") >>
        ( Rule::Suffix(
                rule_text.split('.').map(|s| s.to_string() ).rev().collect(), SuffixType::Exception ) )
    )
);

named!( wildcard_rule<&str, Rule>,
    do_parse!(
        tag!("*.") >>
        rule_text: take_till!(char::is_whitespace) >>
        tag!("\n") >>
        ( Rule::Suffix( rule_text.split('.').map(|s| s.to_string() ).rev().collect(), SuffixType::Wildcard ) )
    )
);

named!( suffix<&str, Rule>,
    do_parse!(
        rule_text: take_till!(char::is_whitespace) >>
        tag!("\n") >>
        ( Rule::Suffix(rule_text.split('.').map(|s| s.to_string() ).rev().collect(), SuffixType::Normal) )
    )
);

named!( ps_line<&str, Rule>,
    alt!(
        division
        |
        comment
        |
        exception_rule
        |
        wildcard_rule
        |
        suffix
    )
);

/// List provides domain parsing capabilities
pub struct List {
    sections: HashMap<String, Vec<Rule>>,
    cache: Cache<String, usize>
}

impl List {
    /// expire internal cache
    pub fn clear_cache(&mut self) {
        self.cache.clear()
    }

    /// parse_domain parses a tld+1 from a domain
    pub fn parse_domain<'a>(&mut self, raw_input: &'a str) -> Option<&'a str> {
        if let Some(dlen) = self.cache.get(raw_input) {
            if *dlen < raw_input.len() {
                return Some(&raw_input[*dlen..]);
            }
        }

        if raw_input.is_empty() {
            return None;
        }

        if raw_input.starts_with('.') {
            return None;
        }

        let input_tokens: Vec<&str> = raw_input.split('.').rev().collect();
        let input_tokens_len = input_tokens.len();

        // 1 Match domain against all rules and take note of the matching ones.
        let mut matches = Vec::with_capacity(100);

        // 2 If no rules match, the prevailing rule is "*".
        // 3 If more than one rule matches, the prevailing rule is the one which is an exception rule.
        // 4 If there is no matching exception rule, the prevailing rule is the one with the most labels.
        // 5 If the prevailing rule is a exception rule, modify it by removing the leftmost label.
        // 6 The public suffix is the set of labels from the domain which match the labels of the prevailing rule, using the matching algorithm above.
        // 7 The registered or registrable domain is the public suffix plus one additional label.
        if let Some(last) = input_tokens.first() {
            let last = last.to_string();
            if let Some(section) = self.sections.get(&last) {
                for rule in section.iter() {
                    if let Rule::Suffix(rule_labels, _ty) = rule {
                        let rlen = rule_labels.len();
                        if rlen > input_tokens_len {
                            continue;
                        }
                        if rule_labels[..] == input_tokens[..rlen] {
                            matches.push(rule);
                        }
                    }
                }
            }
        }

        let rule = {
            let exception = matches.iter().find(|e| {
                if let Rule::Suffix(_, SuffixType::Exception) = e {
                    true
                } else {
                    false
                }
            });

            if exception.is_some() {
                exception
            } else {
                matches.iter().max_by_key(|x| {
                    if let Rule::Suffix(xx, _) = x {
                        xx.len()
                    } else {
                        0usize
                    }
                })
            }
        };

        // Find the position of the domain in the source string, and return that slice
        // to the end, including the match
        let (rule_chars_len, domain_idx) = match rule {
            Some(Rule::Suffix(rule, ty)) => {
                match ty {
                    SuffixType::Wildcard => {
                        let rule_chars_len: usize = rule.iter().map(|i| i.len()).sum();
                        if let Some(domain_token) = input_tokens.get(rule.len()) {
                            let periods = rule.len();
                            let domain_label_len = domain_token.len();
                            let rule_chars_len = rule_chars_len + domain_label_len + periods;
                            let domain_idx = rule.len() + 1;
                            (rule_chars_len, domain_idx)
                        } else {
                            return None;
                        }
                    }
                    SuffixType::Exception => {
                        // throw away first token of rule, since it's an exception
                        let rule = &rule[..rule.len() - 1];
                        let rule_chars_len: usize = rule.iter().map(|i| i.len()).sum();
                        let periods = rule.len() - 1;
                        let rule_chars_len = rule_chars_len + periods;
                        (rule_chars_len, rule.len())
                    }
                    SuffixType::Normal => {
                        let rule_chars_len: usize = rule.iter().map(|i| i.len()).sum();
                        let periods = rule.len() - 1;
                        let rule_chars_len = rule_chars_len + periods;
                        (rule_chars_len, rule.len())
                    }
                }
            }
            _ => {
                // If no rule matches, "*" rule (one level) prevails
                let rule: [&str; 0] = [];
                let rule_chars_len: usize = rule.iter().map(|i| i.len()).sum();
                match input_tokens.get(rule.len()) {
                    Some(domain_token) => {
                        let periods = rule.len();
                        let domain_label_len = domain_token.len();
                        let rule_chars_len = rule_chars_len + domain_label_len + periods;
                        let domain_idx = rule.len() + 1;
                        (rule_chars_len, domain_idx)
                    }
                    None => {
                        return None;
                    }
                }
            }
        };

        if let Some(domain_token) = input_tokens.get(domain_idx) {
            let dlen = raw_input.len() - domain_token.len() - 1 - rule_chars_len;
            if dlen < raw_input.len() {
                self.cache.entry(raw_input.to_string()).or_insert(dlen);
                return Some(&raw_input[dlen..]);
            }
        }

        None
    }

    fn read_file(filepath: &PathBuf) -> io::Result<String> {
        use std::fs::OpenOptions;
        use std::io::Read;
        let mut file = OpenOptions::new().read(true).open(filepath)?;
        let mut contents = String::new();

        file.read_to_string(&mut contents)?;
        Ok(contents)
    }

    /// PUBLIC_SUFFIX_LIST_FILE="some/path/to/file.txt"
    /// parse_source_file Will prefer the env variable to the passed &str path
    pub fn parse_source_file(filename: &str, cache_size: usize, include_private: bool) -> io::Result<Self> {
        let psl_path = env::var("PUBLIC_SUFFIX_LIST_FILE").unwrap_or_else(|_| filename.to_string());

        let path = fs::canonicalize(PathBuf::from(psl_path))?;
        info!("Using public suffix list file: {:?}", path);

        let contents = Self::read_file(&path)?;
        Ok(Self::parse_source(contents, cache_size, include_private))
    }

    fn parse_source(source: String, cache_size: usize, include_private: bool) -> Self {
        let mut sections: HashMap<String, Vec<Rule>> = HashMap::new();
        let mut rest: &str = &source;
        let mut skip_private = false;
        while let Ok((r, rule)) = ps_line(rest) {
            if skip_private { continue; }

            if rule == Rule::Division(Division::PRIVATE(DivisionSep::Begin)) && !include_private { skip_private = true; }
            else if rule == Rule::Division(Division::PRIVATE(DivisionSep::End)) && !include_private { skip_private= false; }

            rest = r;
            if let Rule::Suffix(s, ty) = rule {
                let section = s.first().unwrap();
                let entry = sections.entry(section.clone()).or_insert_with(Vec::new);

                let contains_punycode = {
                    // https://en.wikipedia.org/wiki/Punycode#Separation_of_ASCII_characters
                    s.iter().any(|x| !x.is_ascii())
                };

                if contains_punycode {
                    let s = s.iter().rev().cloned().collect::<Vec<_>>().join(".");
                    let result = idna::domain_to_ascii(&s);
                    if let Ok(encoded) = result {
                        let encoded_with_newline = format!("{}\n", encoded);
                        let synth_rule = ps_line(&encoded_with_newline);
                        if let Ok((_, Rule::Suffix(synth_rule, ty))) = synth_rule {
                            entry.push(Rule::Suffix(synth_rule.clone(), ty));
                        }
                    }
                }

                entry.push(Rule::Suffix(s.clone(), ty));
            }
        }

        List {
            sections,
            cache: Cache::new(cache_size)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_domain() {
        let example = "am\ncom.am\n!gov.am\n*.net.am\n";
        let mut list = List::parse_source(example.to_string(), 10, true);
        let domain = "sub.example.com.am";

        let parsed_domain = list.parse_domain(domain);

        assert_eq!(parsed_domain, Some("example.com.am"));
    }

    #[test]
    fn test_parse_list() {
        let example = "am\ncom.am\n!gov.am\n*.com.am\n";
        let parsed = List::parse_source(example.to_string(), 10, true);
        assert_eq!(
            parsed.sections.get("am"),
            Some(&vec![
                Rule::Suffix(vec!["am".to_string()], SuffixType::Normal),
                Rule::Suffix(
                    vec!["am".to_string(), "com".to_string()],
                    SuffixType::Normal
                ),
                Rule::Suffix(
                    vec!["am".to_string(), "gov".to_string()],
                    SuffixType::Exception
                ),
                Rule::Suffix(
                    vec!["am".to_string(), "com".to_string()],
                    SuffixType::Wildcard
                ),
            ])
        );
    }

    #[test]
    fn division() {
        let commentline = "// ===BEGIN ICANN DOMAINS===\n";
        let start = ps_line(commentline);
        let expected = Rule::Division(Division::ICANN(DivisionSep::Begin));
        assert_eq!(start, Ok(("", expected)));
    }

    #[test]
    fn comments() {
        let commentline = "//this is a comment\n";
        let start = ps_line(commentline);
        assert_eq!(
            start,
            Ok(("", Rule::Comment("this is a comment".to_string()))),
            "testing comments"
        );
    }

    #[test]
    fn exception_rule_line() {
        let start = ps_line("!www.ck\n");
        assert_eq!(
            start,
            Ok((
                "",
                Rule::Suffix(
                    vec!["ck".to_string(), "www".to_string()],
                    SuffixType::Exception
                )
            )),
            "testing exception rules"
        );
    }

    #[test]
    fn wildcard_rule_line() {
        let start = ps_line("*.ck\n");
        assert_eq!(
            start,
            Ok((
                "",
                Rule::Suffix(vec!["ck".to_string()], SuffixType::Wildcard)
            )),
            "testing wildcards"
        );
    }

    #[test]
    fn suffix_line() {
        let start = ps_line("edu.ai\n");
        assert_eq!(
            start,
            Ok((
                "",
                Rule::Suffix(
                    vec!["ai".to_string(), "edu".to_string()],
                    SuffixType::Normal
                )
            )),
            "testing suffix lines"
        );
    }

    #[test]
    fn comodo_suite() {
        let mut list = List::parse_source_file("public_suffix_list.dat", 10, true).expect("unable to parse PSL file");

        // Any copyright is dedicated to the Public Domain.
        // https://creativecommons.org/publicdomain/zero/1.0/
        // null input.
        check_public_suffix(&mut list, "", "");
        // Mixed case.

        // NOTE: is one place where we should choose to deviate from the spec:
        // requiring a to_lowercase() call results in an allocation.
        //check_public_suffix(&mut list, "COM", "");
        //check_public_suffix(&mut list, "example.COM", "example.com");
        //check_public_suffix(&mut list, "WwW.example.COM", "example.com");

        // Leading dot.
        check_public_suffix(&mut list, ".com", "");
        check_public_suffix(&mut list, ".example", "");
        check_public_suffix(&mut list, ".example.com", "");
        check_public_suffix(&mut list, ".example.example", "");
        // Unlisted TLD.
        check_public_suffix(&mut list, "example", "");
        check_public_suffix(&mut list, "example.example", "example.example");
        check_public_suffix(&mut list, "b.example.example", "example.example");
        check_public_suffix(&mut list, "a.b.example.example", "example.example");

        // Listed, but non-Internet, TLD.
        //check_public_suffix(&mut list, "local', "");
        //check_public_suffix(&mut list, "example.local', "");
        //check_public_suffix(&mut list, "b.example.local', "");
        //check_public_suffix(&mut list, "a.b.example.local', "");
        // TLD with only 1 rule.
        check_public_suffix(&mut list, "biz", "");
        check_public_suffix(&mut list, "domain.biz", "domain.biz");
        check_public_suffix(&mut list, "b.domain.biz", "domain.biz");
        check_public_suffix(&mut list, "a.b.domain.biz", "domain.biz");
        // TLD with some 2-level rules.
        check_public_suffix(&mut list, "com", "");
        check_public_suffix(&mut list, "example.com", "example.com");
        check_public_suffix(&mut list, "b.example.com", "example.com");
        check_public_suffix(&mut list, "a.b.example.com", "example.com");
        check_public_suffix(&mut list, "uk.com", "");
        check_public_suffix(&mut list, "example.uk.com", "example.uk.com");
        check_public_suffix(&mut list, "b.example.uk.com", "example.uk.com");
        check_public_suffix(&mut list, "a.b.example.uk.com", "example.uk.com");
        check_public_suffix(&mut list, "test.ac", "test.ac");
        // TLD with only 1 (wildcard) rule.
        check_public_suffix(&mut list, "mm", "");

        //NOTE, not present in file!
        check_public_suffix(&mut list, "c.mm", "");
        check_public_suffix(&mut list, "b.c.mm", "b.c.mm");
        check_public_suffix(&mut list, "a.b.c.mm", "b.c.mm");

        // More complex TLD.
        check_public_suffix(&mut list, "jp", "");
        check_public_suffix(&mut list, "test.jp", "test.jp");
        check_public_suffix(&mut list, "www.test.jp", "test.jp");
        check_public_suffix(&mut list, "ac.jp", "");
        check_public_suffix(&mut list, "test.ac.jp", "test.ac.jp");
        check_public_suffix(&mut list, "www.test.ac.jp", "test.ac.jp");
        check_public_suffix(&mut list, "kyoto.jp", "");
        check_public_suffix(&mut list, "test.kyoto.jp", "test.kyoto.jp");
        check_public_suffix(&mut list, "ide.kyoto.jp", "");
        check_public_suffix(&mut list, "b.ide.kyoto.jp", "b.ide.kyoto.jp");
        check_public_suffix(&mut list, "a.b.ide.kyoto.jp", "b.ide.kyoto.jp");

        // NOTE FAILS: why?
        check_public_suffix(&mut list, "c.kobe.jp", "");

        check_public_suffix(&mut list, "b.c.kobe.jp", "b.c.kobe.jp");
        check_public_suffix(&mut list, "a.b.c.kobe.jp", "b.c.kobe.jp");
        check_public_suffix(&mut list, "city.kobe.jp", "city.kobe.jp");
        check_public_suffix(&mut list, "www.city.kobe.jp", "city.kobe.jp");
        // TLD with a wildcard rule and exceptions.
        check_public_suffix(&mut list, "ck", "");
        check_public_suffix(&mut list, "test.ck", "");
        check_public_suffix(&mut list, "b.test.ck", "b.test.ck");
        check_public_suffix(&mut list, "a.b.test.ck", "b.test.ck");
        check_public_suffix(&mut list, "www.ck", "www.ck");
        check_public_suffix(&mut list, "www.www.ck", "www.ck");
        // US K12.
        check_public_suffix(&mut list, "us", "");
        check_public_suffix(&mut list, "test.us", "test.us");
        check_public_suffix(&mut list, "www.test.us", "test.us");
        check_public_suffix(&mut list, "ak.us", "");
        check_public_suffix(&mut list, "test.ak.us", "test.ak.us");
        check_public_suffix(&mut list, "www.test.ak.us", "test.ak.us");
        check_public_suffix(&mut list, "k12.ak.us", "");
        check_public_suffix(&mut list, "test.k12.ak.us", "test.k12.ak.us");
        check_public_suffix(&mut list, "www.test.k12.ak.us", "test.k12.ak.us");
        // IDN labels.
        check_public_suffix(&mut list, "食狮.com.cn", "食狮.com.cn");
        check_public_suffix(&mut list, "食狮.公司.cn", "食狮.公司.cn");
        check_public_suffix(&mut list, "www.食狮.公司.cn", "食狮.公司.cn");
        check_public_suffix(&mut list, "shishi.公司.cn", "shishi.公司.cn");
        check_public_suffix(&mut list, "公司.cn", "");
        check_public_suffix(&mut list, "食狮.中国", "食狮.中国");
        check_public_suffix(&mut list, "www.食狮.中国", "食狮.中国");
        check_public_suffix(&mut list, "shishi.中国", "shishi.中国");
        check_public_suffix(&mut list, "中国", "");
        // Same as above, but punycoded.
        check_public_suffix(&mut list, "xn--85x722f.com.cn", "xn--85x722f.com.cn");
        check_public_suffix(&mut list, "xn--85x722f.xn--55qx5d.cn", "xn--85x722f.xn--55qx5d.cn");
        check_public_suffix(&mut list, "www.xn--85x722f.xn--55qx5d.cn", "xn--85x722f.xn--55qx5d.cn");
        check_public_suffix(&mut list, "shishi.xn--55qx5d.cn", "shishi.xn--55qx5d.cn");
        check_public_suffix(&mut list, "xn--55qx5d.cn", "");
        check_public_suffix(&mut list, "xn--85x722f.xn--fiqs8s", "xn--85x722f.xn--fiqs8s");
        check_public_suffix(&mut list, "www.xn--85x722f.xn--fiqs8s", "xn--85x722f.xn--fiqs8s");
        check_public_suffix(&mut list, "shishi.xn--fiqs8s", "shishi.xn--fiqs8s");
        check_public_suffix(&mut list, "xn--fiqs8s", "");
    }

    fn check_public_suffix(list: &mut List, input: &str, expected: &str) {
        let expected = if expected == "" { None } else { Some(expected) };
        assert_eq!(list.parse_domain(input), expected);
    }

}
