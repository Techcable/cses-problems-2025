use std::collections::BTreeMap;
use std::fmt::{Debug, Formatter};
use std::iter::FromIterator;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let input = input.trim();
    let res = problem(input);
    println!("{}", res.len());
    for val in res {
        println!("{val}");
    }
    Ok(())
}

#[derive(Default, Clone, Eq, PartialEq)]
pub struct CharCounter {
    counts: BTreeMap<char, u32>,
    total: u32,
}
impl CharCounter {
    /// Returns the previous number of entries, or `0` if not previously present.
    pub fn insert_single(&mut self, c: char) -> u32 {
        let new_count = *self.counts.entry(c).and_modify(|c| *c += 1).or_insert(1);
        self.total += 1;
        assert!(new_count > 0);
        new_count - 1
    }
    /// Remove a single element from the map,
    /// packing if not previously present.
    ///
    /// Returns the previous number of entries.
    pub fn remove_single(&mut self, c: char) -> u32 {
        let old_count = self.counts.get(&c).copied();
        match old_count {
            None | Some(0) => panic!("Cannot remove missing char {c:?}"),
            Some(1) => {
                self.total -= 1;
                assert_eq!(self.counts.remove(&c), old_count);
                1
            }
            Some(old_count) => {
                self.total -= 1;
                assert_eq!(self.counts.insert(c, old_count - 1), Some(old_count),);
                old_count
            }
        }
    }
    pub fn iter(&self) -> impl Iterator<Item = (char, u32)> + '_ {
        self.counts.iter().map(|(&k, &v)| (k, v))
    }
}
impl Debug for CharCounter {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}
impl From<String> for CharCounter {
    fn from(s: String) -> Self {
        s.chars().collect()
    }
}
impl From<&'_ str> for CharCounter {
    fn from(s: &'_ str) -> Self {
        s.chars().collect()
    }
}

impl FromIterator<char> for CharCounter {
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> Self {
        // NOTE: Cannot efficiently implement `sorted_by_occurrence` due to need to keep count
        let mut counter = CharCounter::default();
        for item in iter {
            counter.insert_single(item);
        }
        counter
    }
}

pub fn problem(input: &str) -> Vec<String> {
    assert!(!input.is_empty());
    let chars = input.chars().collect::<CharCounter>();
    assert_eq!(chars.total as usize, input.len());
    let expected_len = count_combinations(&chars);
    let mut res = Vec::new();
    generate_reversed(&chars, &mut |s| {
        res.push(s.into_iter().rev().collect());
    });
    assert_eq!(res.len() as u64, expected_len, "{res:?}");
    res
}

fn generate_reversed(chars: &CharCounter, func: &mut dyn FnMut(Vec<char>)) {
    let mut child = chars.clone();
    for (c, orig_count) in chars.iter() {
        child.remove_single(c);
        if child.total == 0 {
            let mut chars = Vec::with_capacity(chars.total as usize);
            chars.push(c);
            func(chars);
        } else {
            generate_reversed(&child, &mut |mut chars| {
                chars.push(c);
                func(chars);
            });
        }
        child.insert_single(c); // restore to pristine state
        assert_eq!(child.counts[&c], orig_count);
        assert_eq!(child.total, chars.total);
    }
}

/// Count the different ways the characters can be combined.
pub fn count_combinations(chars: &CharCounter) -> u64 {
    // If `k_1, k_2, ..., k_n` are the occurrences of the characters
    // and `n = sum k_i` is the length of the string,
    // then the result is the product of
    // `n choose k_1` (picking the location of the most common characters),
    // times `(n - k_1) choose k_2` (picking the location of the next most common chars).
    // times `(n - K_1 - k_2) choose k_3`) etc. until the last characters which are `(k_n choose k_n) == 1`.
    let mut sorted_by_count = chars.iter().collect::<Vec<_>>();
    sorted_by_count.sort_unstable_by_key(|&(c, _)| chars.counts[&c]);
    let (result, remaining) = sorted_by_count.into_iter().map(|(_, count)| count).fold(
        (1u64, chars.total),
        |(acc, remaining), count| {
            assert!(remaining >= count);
            (
                acc * binomial_coefficient(remaining, count),
                remaining - count,
            )
        },
    );
    assert_eq!(remaining, 0);
    result
}

/// Compute the binomial coefficient `a choose b`.
pub fn binomial_coefficient(n: u32, k: u32) -> u64 {
    assert!(k <= n);
    fn fold(acc: u64, item: u32) -> u64 {
        acc * item as u64
    }
    if n == k || k == 0 {
        1
    } else {
        let num = ((n - k + 1)..=n).fold(1, fold);
        let denom = (1..=k).fold(1, fold);
        num / denom
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use indoc::indoc;

    #[test]
    fn binomial_coefficients() {
        assert_eq!(binomial_coefficient(5, 3), 10);
        assert_eq!(binomial_coefficient(10, 5), 252);
    }

    #[test]
    fn count_combos() {
        assert_eq!(count_combinations(&"aabac".into()), 20);
    }

    #[test]
    fn example() {
        assert_eq!(
            problem("aabac"),
            indoc!(
                "
                aaabc
                aaacb
                aabac
                aabca
                aacab
                aacba
                abaac
                abaca
                abcaa
                acaab
                acaba
                acbaa
                baaac
                baaca
                bacaa
                bcaaa
                caaab
                caaba
                cabaa
                cbaaa"
            )
            .lines()
            .map(String::from)
            .collect::<Vec<_>>()
        );
    }
}
