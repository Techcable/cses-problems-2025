use multiset::NumberMultiSet;
use std::hash::{BuildHasherDefault, Hasher};
use std::ops::ControlFlow;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let mut lines = input.lines();
    let num_inputs = lines.next().unwrap().trim().parse::<usize>()?;
    let apple_weights = lines
        .next()
        .unwrap()
        .split_whitespace()
        .map(str::parse::<u32>)
        .collect::<Result<Vec<_>, _>>()?;
    assert_eq!(num_inputs, apple_weights.len());
    let sol = naive_problem(&apple_weights);
    println!("{}", sol.signed_delta());
    if std::env::var_os("NICKNINJA_DEBUG").is_some_and(|x| x == "1") {
        eprintln!("{:?}", sol.left);
        eprintln!("{:?}", sol.right);
    }
    Ok(())
}

pub fn problem(apple_weights: &[u32]) -> Solution {
    let sum = apple_weights.iter().copied().map(u64::from).sum::<u64>();
    let left = knapsack(apple_weights, sum.div_ceil(2));
    let left = NumberMultiSet::from(left.as_slice());
    let mut right = NumberMultiSet::from(apple_weights);
    right.remove_all(&left);
    assert_eq!(
        left.sum() + right.sum(),
        sum,
        "{apple_weights:?} => {left:?}, {right:?}"
    );
    Solution { left, right }
}

pub const MAX_INPUTS: usize = 20;
pub const MAX_WEIGHT: u32 = 10u32.pow(9);

struct Fnv1Hash(std::num::Wrapping<u64>);
impl Fnv1Hash {
    const OFFSET_BASIS: u64 = 0xcbf29ce484222325;
    const PRIME: u64 = 0x00000100000001b3;
}
impl Default for Fnv1Hash {
    #[inline]
    fn default() -> Self {
        Fnv1Hash(std::num::Wrapping(Self::OFFSET_BASIS))
    }
}
impl Hasher for Fnv1Hash {
    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.0 *= Self::PRIME;
        self.0 ^= i as u64;
    }
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for &x in bytes {
            self.write_u8(x);
        }
    }
    #[inline]
    fn finish(&self) -> u64 {
        self.0 .0
    }
}

/// Solves 0-1 knapsack problem using dynamic programming.
pub fn knapsack(items: &[u32], max_weight: u64) -> Vec<u32> {
    type HashMap = std::collections::HashMap<u64, u64, BuildHasherDefault<Fnv1Hash>>;
    assert!(!items.is_empty());
    struct State<'a> {
        /// An map of `max_weight -> last_value` indexed by `end_index`.
        ///
        /// Excludes `end_index = 0`, but includes `end_index = items.len()`.
        /// Hence has length `items.len()`
        cache: Vec<HashMap>,
        items: &'a [u32],
    }
    fn get(state: &State, end_index: usize, max_weight: u64) -> Option<u64> {
        assert!(end_index <= state.items.len());
        if end_index == 0 || max_weight == 0 {
            Some(0)
        } else {
            state.cache[end_index - 1].get(&max_weight).copied()
        }
    }
    fn solve(state: &mut State, end_index: usize, max_weight: u64) -> u64 {
        assert!(end_index <= state.items.len());
        if let Some(existing) = get(state, end_index, max_weight) {
            existing
        } else {
            let new_item = state.items[end_index - 1];
            let res = if u64::from(new_item) > max_weight {
                solve(&mut *state, end_index - 1, max_weight)
            } else {
                let excluding_new_item = solve(&mut *state, end_index - 1, max_weight);
                let including_new_item =
                    solve(&mut *state, end_index - 1, max_weight - u64::from(new_item))
                        + u64::from(new_item);
                if excluding_new_item > including_new_item {
                    excluding_new_item
                } else {
                    including_new_item
                }
            };
            let old_val = state.cache[end_index - 1].insert(max_weight, res);
            assert!(old_val.is_none() || old_val == Some(res), "{old_val:?}");
            res
        }
    }
    fn knapsack(state: &State, end_index: usize, max_weight: u64) -> Vec<u32> {
        // mirrors the solve method but computes the actual set as well
        if end_index == 0 || max_weight == 0 {
            Vec::with_capacity(state.items.len())
        } else {
            let new_item = state.items[end_index - 1];
            if u64::from(new_item) > max_weight {
                knapsack(state, end_index - 1, max_weight)
            } else {
                let weight_excluding_new_item = get(state, end_index - 1, max_weight).unwrap();
                let weight_including_new_item =
                    get(state, end_index - 1, max_weight - u64::from(new_item)).unwrap()
                        + u64::from(new_item);
                if weight_excluding_new_item > weight_including_new_item {
                    knapsack(state, end_index - 1, max_weight)
                } else {
                    let mut list = knapsack(state, end_index - 1, max_weight - u64::from(new_item));
                    list.push(new_item);
                    list
                }
            }
        }
    }
    let mut state = State {
        items,
        cache: vec![HashMap::default(); items.len()],
    };
    let result_sum = solve(&mut state, items.len(), max_weight);
    let set = knapsack(&state, items.len(), max_weight);
    assert_eq!(
        set.iter().copied().map(u64::from).sum::<u64>(),
        result_sum,
        "{set:?}"
    );
    set
}

#[derive(Debug, Clone)]
pub struct Solution {
    left: NumberMultiSet,
    right: NumberMultiSet,
}
impl Solution {
    /// Begin a solution by placing everything on the left side.
    pub fn begin(left: impl Into<NumberMultiSet>) -> Solution {
        Solution {
            left: left.into(),
            right: NumberMultiSet::new(),
        }
    }
    pub fn swap(&mut self) {
        std::mem::swap(&mut self.left, &mut self.right);
    }
    #[track_caller]
    pub fn move_to_right(&mut self, value: u32) {
        self.left.remove(value);
        self.right.insert(value);
    }
    #[track_caller]
    pub fn move_to_left(&mut self, value: u32) {
        self.right.remove(value);
        self.left.insert(value);
    }
    /// The delta for this pair, which is how much bigger the `left` sum is than the `right` sum.
    #[expect(
        clippy::cast_possible_wrap,
        reason = "in this context, u64 -> i64 overflow is exceptionally rare"
    )]
    pub fn signed_delta(&self) -> i64 {
        // cannot use checked_signed_diff on 1.75
        (self.left.sum() as i64) - (self.right.sum() as i64)
    }
    #[inline]
    pub fn abs_delta(&self) -> u64 {
        self.left.sum().abs_diff(self.right.sum())
    }
}

pub fn naive_problem(weights: &[u32]) -> Solution {
    let mut begin = Solution::begin(weights);
    let mut min_result = begin.clone();
    let _ = naive_search(&mut begin, &mut |solution| {
        if solution.abs_delta() < min_result.abs_delta() {
            min_result = solution.clone();
        }
        ControlFlow::Continue(())
    });
    min_result
}

type SuccessCallback<'a> = dyn FnMut(&Solution) -> ControlFlow<()> + 'a;

/// Searches all possible combinations,
/// shrinking the `left` set and growing the right `set`.
///
/// Differs from `naive_search` in 008-two-sets because there is no backtracking.
pub fn naive_search(solution: &mut Solution, func: &mut SuccessCallback) -> ControlFlow<()> {
    if solution.left.is_empty() {
        return ControlFlow::Continue(());
    } else if !solution.right.is_empty() {
        func(solution)?;
    }
    let original_left = solution.left.iter().collect::<Vec<_>>();
    for value in original_left {
        solution.move_to_right(value);
        naive_search(solution, func)?;
        solution.move_to_left(value);
    }
    ControlFlow::Continue(())
}

mod multiset {
    //! Defines the [`NumberMultiSet`] type.
    //!
    //! This is in its own module for better encapsulation.

    use std::cmp::Ordering;
    use std::collections::{btree_map, btree_map::Entry, BTreeMap};
    use std::num::NonZeroUsize;
    use std::ops::{Bound, RangeBounds, RangeInclusive};

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct NumberMultiSet {
        occurrences: BTreeMap<u32, NonZeroUsize>,
        len: usize,
        sum: u64,
    }
    impl NumberMultiSet {
        #[allow(clippy::new_without_default)] // pointless
        pub const fn new() -> NumberMultiSet {
            NumberMultiSet {
                occurrences: BTreeMap::new(),
                len: 0,
                sum: 0,
            }
        }

        #[inline]
        pub fn is_empty(&self) -> bool {
            debug_assert_eq!(self.len == 0, self.occurrences.is_empty());
            self.occurrences.is_empty()
        }

        #[inline]
        pub fn len(&self) -> usize {
            self.len
        }

        #[inline]
        #[track_caller]
        pub fn verify_state(&self) {
            assert_eq!(
                self.iter()
                    .fold((0usize, 0u64), |(old_count, old_sum), entry| {
                        (old_count + 1, old_sum + u64::from(entry))
                    }),
                (self.len, self.sum),
                "unexpected state"
            );
        }

        #[inline]
        pub fn sum(&self) -> u64 {
            self.sum
        }

        pub fn smallest(&self) -> Option<u32> {
            self.occurrences.first_key_value().map(|(&key, _)| key)
        }

        pub fn largest(&self) -> Option<u32> {
            self.occurrences.last_key_value().map(|(&key, _)| key)
        }

        pub fn remove_all(&mut self, other: &NumberMultiSet) {
            self.verify_state();
            for (&key, &other_count) in &other.occurrences {
                let entry = self.occurrences.entry(key);
                let old_count = match entry {
                    Entry::Occupied(ref entry) => entry.get().get(),
                    Entry::Vacant(_) => 0,
                };
                assert!(
                    old_count >= other_count.get(),
                    "Cannot remove {other_count} occurrences of {key}, because this set has only {old_count} occurrences"
                );
                let Entry::Occupied(mut entry) = entry else {
                    unreachable!("vacant not possible because old_count >= other_count > 0")
                };
                match old_count.cmp(&other_count.get()) {
                    Ordering::Less => unreachable!("already checked"),
                    Ordering::Equal => {
                        entry.remove();
                    }
                    Ordering::Greater => {
                        let new_count = old_count - other_count.get();
                        entry.insert(NonZeroUsize::new(new_count).unwrap());
                    }
                }
                self.len -= other_count.get();
            }
            self.sum -= other.sum;
            self.verify_state();
        }

        pub fn range_unique(
            &self,
            range: impl RangeBounds<u32>,
        ) -> impl DoubleEndedIterator<Item = u32> + '_ {
            self.occurrences.range(range).map(|(&key, _)| key)
        }

        pub fn first_below(&self, x: Bound<u32>) -> Option<u32> {
            self.range_unique((Bound::Unbounded, x.as_ref()))
                .next_back()
        }

        pub fn first_above(&self, x: Bound<u32>) -> Option<u32> {
            self.range_unique((x.as_ref(), Bound::Unbounded)).next()
        }

        pub fn contains(&self, x: u32) -> bool {
            self.occurrences.contains_key(&x)
        }

        pub fn to_range_unique(&self) -> Result<RangeInclusive<u32>, RangeConvertError> {
            if self.is_empty() {
                Err(RangeConvertError::Empty)
            } else {
                let smallest = self.smallest().unwrap();
                let largest = self.largest().unwrap();
                assert!(smallest <= largest);
                let value_range = largest - smallest;
                if value_range as usize == self.len() {
                    Ok(smallest..=largest)
                } else {
                    Err(RangeConvertError::NotContiguous)
                }
            }
        }

        #[inline]
        pub fn iter(&self) -> impl Iterator<Item = u32> + '_ {
            self.occurrences
                .iter()
                .flat_map(|(&key, &count)| std::iter::repeat(key).take(count.get()))
        }

        /// Iterate over the elements of this set,
        /// in order from least to greatest.
        #[inline]
        pub fn iter_unique(&self) -> IterUnique<'_> {
            self.occurrences.keys().copied()
        }

        /// Remove a value from this set,
        /// panicking if missing.
        ///
        /// # Panics
        /// If the element is missing
        #[track_caller]
        pub fn remove(&mut self, value: u32) {
            assert!(self.try_remove(value), "missing value {value}");
        }

        /// Remove a value from this set,
        /// returning `true` if successful.
        #[must_use = "result indicates if successful"]
        pub fn try_remove(&mut self, value: u32) -> bool {
            match self.occurrences.entry(value) {
                btree_map::Entry::Occupied(mut entry) => {
                    let old_count = entry.get().get();
                    match old_count {
                        0 => unreachable!(),
                        1 => {
                            entry.remove();
                        }
                        _ => {
                            entry.insert(NonZeroUsize::new(old_count - 1).unwrap());
                        }
                    }
                    self.len -= 1;
                    self.sum -= u64::from(value);
                    true
                }
                btree_map::Entry::Vacant(_) => false,
            }
        }

        /// Insert a value into this set.
        #[track_caller]
        pub fn insert(&mut self, value: u32) {
            match self.occurrences.entry(value) {
                btree_map::Entry::Occupied(mut entry) => {
                    entry.insert(entry.get().checked_add(1).unwrap());
                }
                btree_map::Entry::Vacant(entry) => {
                    entry.insert(NonZeroUsize::new(1).unwrap());
                }
            }
            self.sum += u64::from(value);
            self.len += 1;
        }
    }
    impl From<&[u32]> for NumberMultiSet {
        fn from(value: &[u32]) -> Self {
            value.iter().copied().collect::<NumberMultiSet>()
        }
    }
    impl<const N: usize> From<[u32; N]> for NumberMultiSet {
        fn from(value: [u32; N]) -> Self {
            value.into_iter().collect::<NumberMultiSet>()
        }
    }
    #[derive(Debug, Clone)]
    pub enum RangeConvertError {
        NotContiguous,
        Empty,
    }
    pub type IterUnique<'a> = std::iter::Copied<btree_map::Keys<'a, u32, NonZeroUsize>>;
    impl FromIterator<u32> for NumberMultiSet {
        fn from_iter<T: IntoIterator<Item = u32>>(iter: T) -> Self {
            let iter = iter.into_iter();
            let mut set = NumberMultiSet::new();
            for value in iter {
                set.insert(value);
            }
            set
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[track_caller]
    fn verify_with(
        inputs: &[u32],
        expected_result: u64,
        problem: fn(&[u32]) -> Solution,
    ) -> Solution {
        let actual_result = problem(inputs.as_ref());
        assert_eq!(
            actual_result.abs_delta(),
            expected_result,
            "Unexpected result {actual_result:?} for {inputs:?}"
        );
        actual_result
    }

    #[track_caller]
    fn verify_naive(inputs: impl AsRef<[u32]>, expected_value: u64) -> Solution {
        verify_with(inputs.as_ref(), expected_value, naive_problem)
    }

    #[track_caller]
    fn verify(inputs: impl AsRef<[u32]>, expected_value: u64) -> Solution {
        verify_with(inputs.as_ref(), expected_value, problem)
    }

    #[test]
    fn example() {
        let inputs = [3, 2, 7, 4, 1];
        verify_naive(inputs, 1);
        verify(inputs, 1);
    }

    #[test]
    fn many_duplicates() {
        verify([1, 2, 2, 1, 3, 1, 1], 1);
    }

    #[test]
    fn test1() {
        verify([603, 324, 573, 493, 659, 521, 654, 70, 718, 257], 2);
    }

    #[test]
    fn test2() {
        verify([952, 775, 292, 702, 859, 719, 65, 943, 376, 490], 1);
    }

    #[test]
    fn test3() {
        verify([141, 156, 14, 487, 250, 230, 741, 602, 32, 717], 2);
    }

    #[test]
    fn test4() {
        verify([963, 359, 731, 826, 599, 931, 40, 86, 777, 760], 4);
    }

    #[test]
    fn test5() {
        verify([238, 224, 861, 461, 558, 860, 318, 93, 347, 402], 2);
    }

    #[test]
    fn test6() {
        verify([193, 848, 70, 53, 864, 886, 374, 31, 288, 700], 1);
    }

    #[test]
    fn test7() {
        verify(
            [
                13048212, 423374770, 19874608, 812293014, 860896267, 224937483, 907570920,
                952166494, 450127366, 887381168, 966393898, 102318919, 723213664, 491414754,
                571209206, 99007249, 302987622, 263275846, 36174214, 727737543,
            ],
            8231,
        );
    }

    #[test]
    fn test8() {
        verify(
            [
                314836307, 815098885, 922742346, 53006071, 757943472, 481505203, 354207278,
                175676232, 335088325, 921705085, 231986392, 619406418, 170606376, 498080884,
                415616625, 40905556, 110076295, 642911923, 932231564, 381545587,
            ],
            1188,
        );
    }

    #[test]
    fn test9() {
        verify(
            [
                846261131, 196958704, 824235264, 647587496, 978085759, 882269655, 811438806,
                657727455, 24328597, 474430888, 447727984, 21699367, 842686077, 330551298,
                93526006, 720473844, 163948377, 592752691, 429743319, 68287836,
            ],
            11770,
        );
    }

    #[test]
    fn test10() {
        verify(
            [
                92021619, 792314463, 937735495, 807418830, 589829609, 270804901, 94470968,
                853138862, 817966179, 656206734, 121829906, 137518261, 766263169, 320158086,
                167044551, 860185204, 347066817, 401533984, 755773385, 623993044,
            ],
            4453,
        );
    }

    #[test]
    fn test11() {
        verify(
            [
                452747515, 202201476, 845758891, 733204504, 327861300, 368456549, 64252070,
                494676885, 21095634, 611030397, 913689714, 849191653, 173901982, 954566440,
                40404105, 228316310, 210730656, 631709598, 847867437, 85805975,
            ],
            4881,
        );
    }

    #[test]
    fn test12() {
        verify(
            [
                934033764, 747013925, 113297529, 621350044, 4858224, 896418401, 823418019,
                490285020, 811592918, 318107753, 122431099, 971962557, 68572395, 269437889,
                506050802, 903504371, 908615271, 406858603, 39392057, 816479349,
            ],
            5482,
        );
    }

    #[test]
    fn test13() {
        verify([1000000000], 1000000000);
    }

    #[test]
    fn test14() {
        verify([1, 1], 0);
    }

    #[test]
    fn test15() {
        verify([1], 1);
    }

    #[test]
    fn test16() {
        verify([934033764, 2, 7, 4, 1], 934033750);
    }

    #[test]
    fn test17() {
        verify(
            [
                934033764, 747013925, 113297529, 621350044, 4858224, 896418401, 823418019,
                490285020, 811592918, 318107753, 122431099, 971962557, 68572395, 269437889,
                506050802, 903504371, 908615271, 406858603, 39392057, 816479348,
            ],
            5483,
        );
    }

    #[test]
    fn test18() {
        verify([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 1);
    }
}
