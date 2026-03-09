use crate::set::NumberSet;
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
    println!("{}", problem(&apple_weights).signed_delta());
    Ok(())
}

pub const MAX_INPUTS: usize = 20;
pub const MAX_WEIGHT: u32 = 10u32.pow(9);

pub fn problem(weights: &[u32]) -> Solution {
    minimize(Solution::begin(weights))
}
fn minimize(mut sol: Solution) -> Solution {
    let mut prev_delta = sol.abs_delta();
    while sol.left.sum() != sol.right.sum() {
        prev_delta = sol.abs_delta();
        if sol.left.sum() > sol.right.sum() {
            sol.move_to_right(
                sol.left
                    .closest_number(saturating_cast(sol.abs_delta()))
                    .unwrap(),
            );
        } else {
            sol.move_to_left(
                sol.right
                    .closest_number(saturating_cast(sol.abs_delta()))
                    .unwrap(),
            );
        }
        if sol.abs_delta() >= prev_delta {
            break; // no progress being made
        }
    }
    sol
}
fn saturating_cast(x: u64) -> u32 {
    x.min(u32::MAX as u64) as u32
}

/// Indicates the solution cannot be minimized further.
struct MinimizationFailedError(Solution);

/// Indicates a pair of values in a [`Solution`] that should be swapped,
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Pair(u32, u32);
impl Pair {
    pub fn reversed(self) -> Pair {
        Pair(self.1, self.0)
    }
    /// Computes the effect of applying this pair to [`Solution::signed_delta`].
    ///
    /// Applying pair `(a, b)` produces a new delta `(left.sum() - a + b) - (right.sum() - b + a)`.
    /// Distributing and reassociating gives `(left.sum() - right.sum()) + (-2a + 2b)`
    #[inline]
    pub fn relative_delta(self) -> i64 {
        (self.1 as i64 - self.0 as i64) * 2
    }
    pub fn apply_to(self, sol: &mut Solution) {
        assert_ne!(self, Pair(0, 0), "zero pair is meaningless");
        assert!(
            self.0 == 0 || sol.left.contains(self.0),
            "missing value {a} for {self:?}, {sol:?}",
            a = self.0
        );
        assert!(
            self.1 == 0 || sol.right.contains(self.1),
            "missing value {b} for {self:?}, {sol:?}",
            b = self.1
        );
        if self.0 != 0 {
            sol.move_to_right(self.0);
        }
        if self.1 != 0 {
            sol.move_to_left(self.1);
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum SetIndex {
    Left,
    Right,
}
impl SetIndex {
    #[inline]
    pub fn other(self) -> SetIndex {
        match self {
            SetIndex::Left => SetIndex::Right,
            SetIndex::Right => SetIndex::Left,
        }
    }
}

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
    #[track_caller]
    pub fn move_to(&mut self, dest: SetIndex, value: u32) {
        match dest {
            SetIndex::Left => self.move_to_left(value),
            SetIndex::Right => self.move_to_right(value),
        }
    }
    fn find_number(&self, x: u32) -> Option<SetIndex> {
        match (self.left.contains(x), self.right.contains(x)) {
            (true, true) => panic!("both sets contain {x}"),
            (false, true) => Some(SetIndex::Right),
            (true, false) => Some(SetIndex::Left),
            (false, false) => None,
        }
    }
    pub fn closest_number(&self, tgt: u32) -> u32 {
        pick_closest_opt(
            self.left.closest_number(tgt),
            self.right.closest_number(tgt),
            tgt,
        )
        .expect("empty solution")
    }
    /// The delta for this pair, which is how much bigger the `left` sum is than the `right` sum.
    pub fn signed_delta(&self) -> i64 {
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
    let mut iter = solution.left.detached_iter();
    while let Some(value) = iter.next(&solution.left) {
        solution.move_to_right(value);
        naive_search(solution, func)?;
        solution.move_to_left(value);
    }
    ControlFlow::Continue(())
}

fn pick_closest_opt(a: Option<u32>, b: Option<u32>, tgt: u32) -> Option<u32> {
    Some(match (a, b) {
        (Some(a), Some(b)) if a.abs_diff(tgt) <= b.abs_diff(tgt) => a,
        (Some(a), Some(b)) => b,
        (Some(x), None) | (None, Some(x)) => x,
        (None, None) => return None,
    })
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

        pub fn closest_number(&self, tgt: u32) -> Option<u32> {
            super::pick_closest_opt(
                self.first_above(Bound::Included(tgt)),
                self.first_below(Bound::Included(tgt)),
                tgt,
            )
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
    impl<const N: usize> From<[u32; N]> for NumberSet {
        fn from(value: [u32; N]) -> Self {
            value.into_iter().collect::<NumberSet>()
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
