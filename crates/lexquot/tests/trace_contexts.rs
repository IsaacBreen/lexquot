//! Independent byte-context membership tests for the stronger trace observer.
//! The oracle reads the original DFA tables and enumerates lexical segmentations;
//! it does not use PreparedTrace, canonical residual IDs or trace-language nodes.
use lexquot::trace::{PrepareOptions, PreparedTrace, TraceDfa};
use lexquot::{parse_regex, Vocab};

fn words(alphabet: &[u8], max: usize) -> Vec<Vec<u8>> {
    let mut all = vec![vec![]];
    let mut level = vec![vec![]];
    for _ in 0..max {
        let mut next = Vec::new();
        for w in &level {
            for &b in alphabet {
                let mut x = w.clone();
                x.push(b);
                next.push(x);
            }
        }
        all.extend(next.clone());
        level = next;
    }
    all
}
fn accepts(d: &TraceDfa, word: &[u8]) -> bool {
    let mut s = d.start() as usize;
    for b in word {
        match d.transitions()[s].iter().find(|(byte, _)| byte == b) {
            Some((_, next)) => s = *next as usize,
            None => return false,
        }
    }
    d.accepting()[s]
}
fn sequence(ds: &[TraceDfa], terminals: &[u8], word: &[u8]) -> bool {
    let mut positions = vec![false; word.len() + 1];
    positions[0] = true;
    for &t in terminals {
        let mut next = vec![false; word.len() + 1];
        for begin in 0..=word.len() {
            if positions[begin] {
                for end in begin..=word.len() {
                    if accepts(&ds[t as usize], &word[begin..end]) {
                        next[end] = true;
                    }
                }
            }
        }
        positions = next;
    }
    positions[word.len()]
}
fn check(ds: &[TraceDfa], tokens: &[Vec<u8>], contexts: &[Vec<u8>]) -> usize {
    let v = Vocab::new(
        tokens
            .iter()
            .enumerate()
            .map(|(i, w)| (i as u32, w.clone()))
            .collect(),
    );
    let a = PreparedTrace::new(ds, PrepareOptions::default())
        .unwrap()
        .request(&v)
        .analyze()
        .unwrap();
    let alphabet = (0..ds.len() as u8).collect::<Vec<_>>();
    let terminal_words = words(&alphabet, 3);
    let mut checks = 0;
    for (i, token) in tokens.iter().enumerate() {
        let class = a.token_class(i as u32).unwrap();
        let other = &tokens[a.representatives[class as usize] as usize];
        if token == other {
            continue;
        }
        for left in contexts {
            for right in contexts {
                let x = [left.as_slice(), token.as_slice(), right.as_slice()].concat();
                let y = [left.as_slice(), other.as_slice(), right.as_slice()].concat();
                for terminals in &terminal_words {
                    assert_eq!(
                        sequence(ds, terminals, &x),
                        sequence(ds, terminals, &y),
                        "G={terminals:?}, x={x:?}, y={y:?}"
                    );
                    checks += 1;
                }
            }
        }
    }
    checks
}
#[test]
fn canonical_merges_preserve_raw_dfa_grammar_membership_in_both_byte_contexts() {
    let tokens = words(b"abc", 3)
        .into_iter()
        .filter(|w| !w.is_empty())
        .collect::<Vec<_>>();
    let contexts = words(b"abc", 2);
    let mut checks = 0;
    for patterns in [
        ["[ab]+", "c", "cc"],
        ["a[bc]*", "[bc]+", "aa"],
        ["[abc]{1,3}", "ab", "bc"],
    ] {
        let ds = patterns
            .iter()
            .map(|s| TraceDfa::from_expression(&parse_regex(s, false)).unwrap())
            .collect::<Vec<_>>();
        checks += check(&ds, &tokens, &contexts);
    }
    assert!(
        checks > 10_000,
        "must check real nontrivial merges, not only singleton classes"
    );
}
#[test]
fn generated_raw_automata_agree_with_context_substitution_for_every_merged_token() {
    let tokens = words(b"ab", 4)
        .into_iter()
        .filter(|w| !w.is_empty())
        .collect::<Vec<_>>();
    let contexts = words(b"ab", 1);
    let mut seed = 92731u64;
    let mut random = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    for _case in 0..40 {
        let mut ds = Vec::new();
        for _ in 0..3 {
            let n = 3 + (random() % 3) as usize;
            let finals = (0..n)
                .map(|s| s > 0 && (s == 1 || random() % 2 == 0))
                .collect();
            let transitions = (0..n)
                .map(|_| {
                    b"ab"
                        .iter()
                        .map(|&b| (b, (random() % n as u64) as u32))
                        .collect()
                })
                .collect();
            // Empty positive languages are rejected by construction; force a
            // reachable final without requiring any particular minimization.
            let mut d: Vec<Vec<(u8, u32)>> = transitions;
            d[0][0].1 = 1;
            ds.push(TraceDfa::new(0, finals, d).unwrap());
        }
        check(&ds, &tokens, &contexts);
    }
}
