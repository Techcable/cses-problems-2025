//! Solves the [CSES Permutation Problem](https://cses.fi/problemset/task/1070)
//!
//! Since inputs can be up to 1 million,
//! it is not computationally feasible to check all `10^6!` possibilities
#![allow(clippy::format_push_string)]

use std::collections::VecDeque;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let input = input.trim().parse::<u32>()?;
    match find_beautiful_permutation(input) {
        Ok(res) => {
            let out = res.iter().fold(String::new(), |mut acc, x| {
                if !acc.is_empty() {
                    acc.push(' ');
                }
                acc.push_str(&format!("{x}"));
                acc
            });
            print!("{out}");
        }
        Err(_) => {
            println!("NO SOLUTION");
        }
    }

    Ok(())
}

#[derive(Debug, Eq, PartialEq)]
struct MissingBeautifulPermutation(u32);
fn find_beautiful_permutation(n: u32) -> Result<Vec<u32>, MissingBeautifulPermutation> {
    match n {
        0 => Ok(vec![]),
        1 => Ok(vec![1]),
        2 | 3 => {
            // cannot of find beautiful permutation of [1, 2] or [1, 2, 3]
            Err(MissingBeautifulPermutation(n))
        }
        _ => {
            let mut perm = VecDeque::<u32>::from([2, 4, 1, 3]);
            while perm.len() < n as usize {
                let new_element = u32::try_from(perm.len() + 1).unwrap();
                if is_conflicting(*perm.back().unwrap(), new_element) {
                    assert!(!is_conflicting(*perm.front().unwrap(), new_element));
                    perm.push_front(new_element);
                } else {
                    perm.push_back(new_element);
                }
            }
            Ok(perm.iter().copied().collect())
        }
    }
}

#[inline]
fn is_conflicting(a: u32, b: u32) -> bool {
    (a as i64 - b as i64).wrapping_abs() == 1
}

#[cfg(test)]
mod test {
    #![allow(clippy::pedantic, clippy::all)] // already submitted & written before clippy was run with --tests
    use super::*;
    use itertools::Itertools;

    #[test]
    fn edge_case_conflicts() {
        assert!(!is_conflicting(u32::MAX, 0));
        assert!(is_conflicting(u32::MAX, u32::MAX - 1));
        assert!(!is_conflicting(u32::MAX - 1, u32::MAX - 1));
        assert!(!is_conflicting(u32::MAX - 1, 0));
        assert!(!is_conflicting(0, 2));
        assert!(is_conflicting(0, 1));
        assert!(is_conflicting(1, 0));
        assert!(!is_conflicting(2, 0));
        // not really well-defined, but shouldn't panic
        assert!(!is_conflicting(0, 0));
        assert!(!is_conflicting(u32::MAX, u32::MAX))
    }

    fn is_valid_beautiful_permutation(x: &[u32]) -> bool {
        x.iter()
            .copied()
            .tuple_windows()
            .all(|(a, b)| (a as i32 - b as i32).abs() > 1)
    }

    fn expect_valid_permutation(n: u32) {
        let actual =
            find_beautiful_permutation(n).expect("expected to find a beautiful permutation");
        assert!(is_valid_beautiful_permutation(&actual), "{n}: {actual:?}")
    }

    #[test]
    fn basic() {
        expect_valid_permutation(1);
        expect_valid_permutation(5);
        expect_valid_permutation(10);
        expect_valid_permutation(60);
    }

    /// Exhaustively search for beautiful permutations.
    ///
    /// Only feasible for small numbers less than around 10.
    fn exhaustively_find_beautiful_permutation(n: u32) -> Option<Vec<u32>> {
        for perm in (1..=n).permutations(n as usize) {
            if is_valid_beautiful_permutation(&perm) {
                return Some(perm);
            }
        }
        None
    }

    #[test]
    fn timeout_large_input() {
        expect_valid_permutation(247250)
    }

    #[test]
    fn no_permutations_2_or_3() {
        assert_eq!(exhaustively_find_beautiful_permutation(2), None);
        assert_eq!(exhaustively_find_beautiful_permutation(3), None);
        assert_eq!(
            find_beautiful_permutation(2),
            Err(MissingBeautifulPermutation(2))
        );
        assert_eq!(
            find_beautiful_permutation(3),
            Err(MissingBeautifulPermutation(3))
        );
    }
}
