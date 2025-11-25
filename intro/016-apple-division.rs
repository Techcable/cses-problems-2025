use crate::set::NumberSet;
use std::collections::Bound;
use std::ops::ControlFlow;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let mut lines = input.lines();
    let num_inputs = lines.next().unwrap().trim().parse::<usize>()?;
    let apple_weights = lines
        .next()
        .unwrap()
        .trim()
        .split_whitespace()
        .map(|entry| entry.parse::<u32>())
        .collect::<Result<Vec<_>, _>>()?;
    assert_eq!(num_inputs, apple_weights.len());
    println!("{}", problem(&apple_weights).delta());
    Ok(())
}

pub const MAX_INPUTS: usize = 20;
pub const MAX_WEIGHT: u32 = 10u32.pow(9);

pub fn problem(weights: &[u32]) -> Solution {
    let mut solution = Solution::begin(weights);
    loop {
        let prev_delta = solution.delta();
        match minimize_difference(solution) {
            Ok(reduced) => {
                assert!(reduced.delta() < prev_delta);
                solution = reduced;
            }
            Err(MinimizationFailedError(minimal)) => return minimal,
        }
    }
}

/// Minimize the difference between the two values, returning
fn minimize_difference(mut solution: Solution) -> Result<Solution, MinimizationFailedError> {
    if solution.delta() == 0 {
        // already minimal
        return Err(MinimizationFailedError(solution));
    }
    assert!(!solution.left.is_empty() || !solution.right.is_empty());
    let delta = solution.delta();
    /// Minimize two optional values, returning `None` only if both inputs are `None`..
    fn minimize_opt_by<T, K: Ord>(
        x: Option<T>,
        y: Option<T>,
        mut func: impl FnMut(&T) -> K,
    ) -> Option<T> {
        match (x, y) {
            (Some(a), Some(b)) => Some(if func(&a) < func(&b) { a } else { b }),
            (Some(y), None) | (None, Some(y)) => Some(y),
            (None, None) => None,
        }
    }
    fn closest_of(set: &NumberSet, x: u64) -> Option<u32> {
        let Ok(x) = u32::try_from(x) else {
            return set.largest();
        };
        minimize_opt_by(
            set.first_below(Bound::Excluded(x)),
            set.first_above(Bound::Excluded(x)),
            |y| y.abs_diff(x),
        )
    }
    // Find a number in left, right closest to delta/2, then see which one that improves our solution
    // rounding is not a problem here, because in the worst case true value is x.5 => x,
    // and we end up picking x over (x + 1)
    let half_delta = delta / 2;
    fn delta_after_move(src: &NumberSet, dest: &NumberSet, value: u32) -> u64 {
        debug_assert!(src.contains(value), "invalid move of {value}");
        let value = value as u64;
        (src.sum() - value).abs_diff(dest.sum() + value)
    }
    fn delta_move_to_right(set: &Solution, value: u32) -> u64 {
        delta_after_move(&set.left, &set.right, value)
    }
    fn delta_move_to_left(set: &Solution, value: u32) -> u64 {
        delta_after_move(&set.right, &set.left, value)
    }
    // find the closest value we want to move, normalizing the solution so that we move from left to right
    let (closest, new_delta) = {
        let closest_left = closest_of(&solution.left, half_delta);
        let closest_right = closest_of(&solution.right, half_delta);
        match (closest_left, closest_right) {
            (Some(closest_left), Some(closest_right)) => {
                let delta_move_to_right = delta_move_to_right(&solution, closest_left);
                let delta_move_to_left = delta_move_to_left(&solution, closest_right);
                if delta_move_to_left < delta_move_to_right {
                    // swap so that the left has the closest value and we move to the right
                    solution.swap();
                    (closest_right, delta_move_to_left)
                } else {
                    (closest_left, delta_move_to_right)
                }
            }
            (Some(closest_left), None) => {
                (closest_left, delta_move_to_right(&solution, closest_left))
            }
            (None, Some(closest_right)) => {
                solution.swap();
                (closest_right, delta_move_to_right(&solution, closest_right))
            }
            (None, None) => unreachable!("both sets are empty for {solution:?}"),
        }
    };
    if new_delta < delta {
        solution.move_to_right(closest);
        Ok(solution)
    } else {
        Err(MinimizationFailedError(solution))
    }
}

/// Indicates the solution cannot be minimized further.
struct MinimizationFailedError(Solution);

#[derive(Debug, Clone)]
pub struct Solution {
    left: NumberSet,
    right: NumberSet,
}
impl Solution {
    /// Begin a solution by placing everything on the left side.
    pub fn begin(left: impl Into<NumberSet>) -> Solution {
        Solution {
            left: left.into(),
            right: NumberSet::new(),
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
    #[inline]
    pub fn delta(&self) -> u64 {
        self.left.sum().abs_diff(self.right.sum())
    }
}

pub fn naive_problem(weights: &[u32]) -> Solution {
    let mut begin = Solution::begin(weights);
    let mut min_result = begin.clone();
    let _ = naive_search(&mut begin, &mut |solution| {
        if solution.delta() < min_result.delta() {
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
    let mut iter = solution.left.detached_iter();
    while let Some(value) = iter.next(&solution.left) {
        solution.move_to_right(value);
        naive_search(solution, func)?;
        solution.move_to_left(value);
    }
    ControlFlow::Continue(())
}

mod set {
    //! Defines the [`NumberSet`] type.
    //!
    //! This is in its own module for better encapsulation.
    use std::collections::{btree_set, BTreeSet};
    use std::ops::{Bound, RangeBounds, RangeInclusive};

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct NumberSet {
        values: BTreeSet<u32>,
        sum: u64,
    }
    impl NumberSet {
        #[allow(clippy::new_without_default)] // pointless
        pub const fn new() -> NumberSet {
            NumberSet {
                values: BTreeSet::new(),
                sum: 0,
            }
        }

        #[inline]
        pub fn is_empty(&self) -> bool {
            self.values.is_empty()
        }

        #[inline]
        pub fn len(&self) -> usize {
            self.values.len()
        }

        #[inline]
        pub fn sum(&self) -> u64 {
            self.sum
        }

        pub fn smallest(&self) -> Option<u32> {
            self.values.first().copied()
        }

        pub fn largest(&self) -> Option<u32> {
            self.values.last().copied()
        }

        pub fn range(
            &self,
            range: impl RangeBounds<u32>,
        ) -> impl DoubleEndedIterator<Item = u32> + '_ {
            self.values.range(range).copied()
        }

        pub fn first_below(&self, x: Bound<u32>) -> Option<u32> {
            self.range((Bound::Unbounded, x.as_ref())).next_back()
        }

        pub fn first_above(&self, x: Bound<u32>) -> Option<u32> {
            self.range((x.as_ref(), Bound::Unbounded)).next()
        }

        pub fn contains(&self, x: u32) -> bool {
            self.values.contains(&x)
        }

        pub fn to_range(&self) -> Result<RangeInclusive<u32>, RangeConvertError> {
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

        /// Iterate over the elements of this set,
        /// in order from least to greatest.
        #[inline]
        pub fn iter(&self) -> Iter<'_> {
            self.values.iter().copied()
        }

        /// Iterate over the elements of this set,
        /// without borrowing the input
        #[inline]
        pub fn detached_iter(&self) -> DetachedIter {
            DetachedIter {
                expected_len: self.values.len(),
                expected_sum: self.sum,
                last: None,
            }
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
            let success = self.values.remove(&value);
            if success {
                self.sum -= value as u64;
            }
            success
        }

        /// Insert a value into this set,
        /// panicking if already present.
        #[track_caller]
        pub fn insert(&mut self, value: u32) {
            assert!(self.try_insert(value), "value {value} already present");
        }

        /// Insert a value into this set,
        /// returning `true` if successful
        /// or `false` if already present
        #[must_use = "result indicates if successful"]
        pub fn try_insert(&mut self, value: u32) -> bool {
            let success = self.values.insert(value);
            if success {
                self.sum += value as u64;
            }
            success
        }
    }
    impl From<&[u32]> for NumberSet {
        fn from(value: &[u32]) -> Self {
            value.iter().copied().collect::<NumberSet>()
        }
    }
    impl IntoIterator for NumberSet {
        type Item = u32;
        type IntoIter = btree_set::IntoIter<u32>;
        fn into_iter(self) -> Self::IntoIter {
            self.values.into_iter()
        }
    }
    #[derive(Debug, Clone)]
    pub enum RangeConvertError {
        NotContiguous,
        Empty,
    }
    pub type Iter<'a> = std::iter::Copied<btree_set::Iter<'a, u32>>;
    /// A detached iterator over a [`NumberSet`] that doesn't borrow its input.
    ///
    /// If the set is unexpectedly modified during iteration,
    /// this will either panic or return unexpected results.
    pub struct DetachedIter {
        expected_len: usize,
        expected_sum: u64,
        last: Option<u32>,
    }
    impl DetachedIter {
        #[track_caller]
        pub fn next(&mut self, set: &NumberSet) -> Option<u32> {
            assert_eq!(
                (set.len(), set.sum()),
                (self.expected_len, self.expected_sum),
                "set changed unexpectedly while iterator was detached"
            );
            match self.last {
                None => {
                    let res = set.values.first().copied();
                    self.last = res;
                    res
                }
                Some(ref last) => {
                    let mut range = set.values.range((Bound::Excluded(*last), Bound::Unbounded));
                    let res = range.next().copied();
                    self.last = res;
                    res
                }
            }
        }
    }
    impl FromIterator<u32> for NumberSet {
        fn from_iter<T: IntoIterator<Item = u32>>(iter: T) -> Self {
            let iter = iter.into_iter();
            let mut set = BTreeSet::new();
            let mut sum = 0u64;
            for value in iter {
                set.insert(value);
                sum = sum.checked_add(value as u64).expect("sum overflow");
            }
            NumberSet { sum, values: set }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[track_caller]
    fn verify_with(inputs: &[u32], expected_result: u64, problem: fn(&[u32]) -> Solution) {
        let actual_result = problem(inputs.as_ref());
        assert_eq!(
            actual_result.delta(),
            expected_result,
            "Unexpected result {actual_result:?} for {inputs:?}"
        )
    }

    #[track_caller]
    fn verify_naive(inputs: impl AsRef<[u32]>, expected_value: u64) {
        verify_with(inputs.as_ref(), expected_value, naive_problem)
    }

    #[track_caller]
    fn verify(inputs: impl AsRef<[u32]>, expected_value: u64) {
        verify_with(inputs.as_ref(), expected_value, problem)
    }

    #[test]
    fn example() {
        let inputs = [3, 2, 7, 4, 1];
        verify_naive(inputs, 1);
        verify(inputs, 1);
    }

    #[test]
    fn test1() {
        verify([603, 324, 573, 493, 659, 521, 654, 70, 718, 257], 2);
    }
}
