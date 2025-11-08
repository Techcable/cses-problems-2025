use std::collections::{BTreeMap, HashSet};

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let input = input.trim();
    assert!(input.chars().all(char::is_alphanumeric));
    match problem(input) {
        Some(result) => println!("{result}"),
        None => println!("NO SOLUTION"),
    }
    Ok(())
}

pub const MAX_INPUT: usize = 10usize.pow(6);
/// Produces a palindrome from the specified string.
///
/// In order for a palindrome to exist, all characters except one must occur an even number of times.
/// If this is not the case, this function will return `None`.
///
/// This function is pure, depending only on the input.
/// When successful, the first half of the string will be in sorted order.
pub fn problem(text: &str) -> Option<String> {
    // use BTreeMap for consistent ordering of counts
    // this means the result will be sorted
    let mut counts: BTreeMap<char, usize> = BTreeMap::new();
    // order doesn't matter here because we fail if there are multiple entries
    let mut odd: HashSet<char> = HashSet::new();
    for c in text.chars() {
        let count = counts.entry(c).or_insert(0);
        *count += 1;
        if *count % 2 != 0 {
            odd.insert(c);
        } else {
            odd.remove(&c);
        }
    }
    if odd.len() > 1 {
        None
    } else {
        let odd = odd.iter().copied().next();
        let even = counts.iter().filter(|&(&c, _)| Some(c) != odd);
        let even_with_multiplicity = even.flat_map(|(&c, &occurrences)| {
            assert_eq!(occurrences % 2, 0);
            std::iter::repeat(c).take(occurrences / 2)
        });
        let even_half = even_with_multiplicity.collect::<String>();
        let mut result = even_half.clone();
        result.extend(odd); // add odd char (if any)
        result.extend(even_half.chars().rev());
        Some(result)
    }
}

pub fn is_palindrome<T: Eq, I>(items: I) -> bool
where
    I: IntoIterator<Item = T>,
    I::IntoIter: Clone + DoubleEndedIterator,
{
    let items = items.into_iter();
    items.clone().zip(items.rev()).all(|(x, y)| x == y)
}

#[cfg(test)]
mod test {
    use crate::{is_palindrome, problem, MAX_INPUT};

    /// Tests the [`is_palindrome`] function.
    #[test]
    fn is_palindrome_predicate() {
        assert!(is_palindrome([1, 2, 1]));
        assert!(!is_palindrome([5, 2, 1]));
        assert!(is_palindrome([2, 8, 8, 2]));
        assert!(is_palindrome("AACABACAA".chars()));
        assert!(is_palindrome("AAACBCAAA".chars()));
        assert!(!is_palindrome("AAAACACBA".chars()));
    }

    fn check(t: &str) -> Option<String> {
        let res = problem(t);
        if let Some(ref res) = res {
            assert!(
                is_palindrome(res.chars()),
                "expected a palindrome from problem({t:?}), but got {res:?}"
            );
        }
        res
    }

    #[track_caller]
    fn require_success(t: &str) -> String {
        check(t).unwrap_or_else(|| panic!("Failed to produce palindrome from {t:?}"))
    }

    #[track_caller]
    fn require_failure(t: &str) {
        match check(t) {
            Some(res) => {
                panic!("Expected problem({t:?}) to fail, but is_palindrome({res:?}) == true")
            }
            None => {}
        }
    }

    #[test]
    fn example() {
        assert_eq!(require_success("AAAACACBA"), "AAACBCAAA");
    }

    #[test]
    fn timeout_max_input() {
        // intentionally excludes letter 'Z'
        let letters = 'A'..='Y';
        assert!(!letters.contains(&'Z'));
        let palindrome = letters
            .clone()
            .cycle()
            .take(MAX_INPUT / 2)
            .chain(letters.rev().cycle().take(MAX_INPUT / 2))
            .collect::<String>();
        assert!(palindrome.is_ascii());
        assert!(palindrome.len().is_multiple_of(2));
        assert!(palindrome.len() <= MAX_INPUT);
        require_success(&palindrome);
        let non_palindrome = std::iter::once('Z')
            .chain(palindrome[1..].chars())
            .collect::<String>();
        require_failure(&non_palindrome);
    }

    #[test]
    fn test1() {
        let x = "AAAAAAAAAA";
        assert_eq!(require_success("AAAAAAAAAA"), x);
    }

    #[test]
    fn test5() {
        require_failure("MWNYFUIRUX");
    }

    #[test]
    fn test3() {
        assert_eq!(require_success("CBPPBFCFAA"), "ABCFPPFCBA");
    }
}
