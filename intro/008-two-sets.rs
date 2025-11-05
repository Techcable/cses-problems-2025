use crate::set::NumberSet;
use std::cmp::Ordering;
use std::ops::{Bound, ControlFlow, Range, RangeBounds, RangeInclusive};

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let input = input.trim().parse::<u32>()?;
    let range = 1..=input;
    fn print_set<I: IntoIterator<Item = u32>>(x: I) {
        let x = x.into_iter().collect::<Vec<_>>();
        assert!(!x.is_empty());
        println!("{}", x.len());
        for (index, val) in x.iter().enumerate() {
            if index > 0 {
                print!(" ");
            }
            print!("{val}");
        }
        println!();
    }
    match intelligent_split(range) {
        None => {
            println!("NO");
        }
        Some((left, right)) => {
            println!("YES");
            print_set(left);
            print_set(right);
        }
    }
    Ok(())
}

type SuccessCallback<'a> = dyn FnMut(&NumberSet, &NumberSet) -> ControlFlow<()> + 'a;

pub fn naive_split(left: RangeInclusive<u32>) -> Option<(NumberSet, NumberSet)> {
    let mut left = left.collect::<NumberSet>();
    let mut right = NumberSet::new();
    let orig_sum = left.sum();
    let mut split = None;
    let control = naive_search(&mut left, &mut right, &mut |left, right| {
        assert_eq!(left.sum() + right.sum(), orig_sum);
        split = Some((left.clone(), right.clone()));
        ControlFlow::Break(())
    });
    match control {
        ControlFlow::Continue(()) => None,
        ControlFlow::Break(()) => Some(split.unwrap()),
    }
}

/// Searches all possible combinations using backtracking,
/// shrinking the `left` set and growing the right `set`.
pub fn naive_search(
    left: &mut NumberSet,
    right: &mut NumberSet,
    func: &mut SuccessCallback,
) -> ControlFlow<()> {
    if right.is_empty() && left.sum() % 2 != 0 {
        // cannot find answer if sum is odd
        return ControlFlow::Continue(());
    }
    let mut iter = left.detached_iter();
    while let Some(value) = iter.next(left) {
        left.remove(value);
        right.insert(value);
        match left.sum().cmp(&right.sum()) {
            Ordering::Less => {
                // backtrack, because shrinking the 'left' when left < right
                // will never cause sums to become equal
            }
            Ordering::Equal => {
                let _: () = func(left, right)?;
            }
            Ordering::Greater => {
                // TODO: This will likely blow the stack for `MAX_INPUT` :/
                let _: () = naive_search(left, right, func)?;
            }
        }
        right.remove(value);
        left.insert(value);
    }
    ControlFlow::Continue(())
}

pub fn intelligent_split(original: RangeInclusive<u32>) -> Option<(NumberSet, NumberSet)> {
    assert!(!original.is_empty(), "{original:?}");
    assert_eq!(*original.start(), 1, "{original:?}");
    let total_sum = sum_range(original.clone());
    if total_sum % 2 != 0 {
        return None;
    }
    let half_sum = total_sum / 2;

    // the idea is to gradually grow the `right`
    // set by taking the largest possible number from the `right`.
    //
    // As an optimization,see how many contiguous numbers we can chunk off the end of left
    // while still remaining under the `half_sum`
    let (mut left, mut right) = {
        assert!(
            *original.end() as u64 <= half_sum,
            "end of range {original:?} exceeds half sum {half_sum}"
        );
        // the lowest element in the range of contiguous elements being split off,
        // we don't need an option since we can always split off the last element
        let mut lowest_contig_element: u32 = *original.end();
        let mut contiguous_elements_sum: u64 = lowest_contig_element as u64;
        for new_last in original.clone().rev().skip(1) {
            debug_assert_eq!(new_last, lowest_contig_element - 1);
            let new_sum = contiguous_elements_sum + new_last as u64;
            if new_sum <= half_sum {
                // we can add to the range of contiguous elements
                lowest_contig_element = new_last;
                contiguous_elements_sum = new_sum;
            } else {
                break;
            }
        }
        assert!(contiguous_elements_sum <= half_sum);
        let (remaining_range, contiguous_elements) = split_range(original, lowest_contig_element);
        assert_eq!(
            sum_range(contiguous_elements.clone()),
            contiguous_elements_sum
        );
        assert_eq!(
            sum_range(remaining_range.clone()),
            total_sum - contiguous_elements_sum
        );
        (
            NumberSet::from(remaining_range),
            NumberSet::from(contiguous_elements),
        )
    };
    loop {
        match left.sum().cmp(&half_sum) {
            Ordering::Greater => {
                let shrink_by = left.sum() - half_sum;
                assert!(shrink_by > 0);
                let shrink_by_u32 = u32::try_from(shrink_by).ok().unwrap_or(u32::MAX);
                match left.first_below(Bound::Included(shrink_by_u32)) {
                    None => {
                        return None;
                    }
                    Some(value) => {
                        assert!(value as u64 <= shrink_by);
                        left.remove(value);
                        right.insert(value);
                    }
                }
            }
            Ordering::Equal => return Some((left, right)),
            Ordering::Less => return None,
        }
    }
}

/// Split the range `[a, b]` into `[a, mid)` and `[mid, b]`
#[inline]
pub fn split_range<T: sealed::PrimInt>(
    range: RangeInclusive<T>,
    mid: T,
) -> (Range<T>, RangeInclusive<T>) {
    assert!(
        *range.start() <= mid && mid <= *range.end(),
        "invalid args: ({range:?}, {mid})"
    );
    (*range.start()..mid, mid..=*range.end())
}
mod sealed {
    use std::fmt::{Debug, Display};
    pub trait PrimInt: Copy + Display + Debug + Ord {}
    impl PrimInt for u32 {}
}

/// Sum all the values in the specified range.
///
/// Equivalent to `range.sum()` but takes O(1) time.
#[inline]
pub fn sum_range<R: RangeBounds<u32>>(range: R) -> u64 {
    let Bound::Included(&start) = range.start_bound() else {
        unimplemented!("start bound must be inclusive: {:?}", range.start_bound());
    };
    let len = match range.end_bound() {
        Bound::Included(&end) => {
            assert!(end >= start);
            (end - start) + 1
        }
        Bound::Excluded(&end) => {
            assert!(end >= start);
            end - start
        }
        Bound::Unbounded => panic!("end bound can't be unbounded"),
    } as u64;
    // special-case is needed to avoid integer underflow
    if len == 0 {
        0
    } else {
        (len * start as u64) + ((len * (len - 1)) / 2)
    }
}

pub const MAX_INPUT: u32 = 10u32.pow(6);

mod set {
    //! Defines the [`NumberSet`] type.
    //!
    //! This is in its own module for better encapsulation.
    use super::sum_range;
    use std::collections::{btree_set, BTreeSet};
    use std::ops::{Bound, Range, RangeInclusive};

    #[derive(Clone, Debug)]
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

        pub fn first_below(&self, x: Bound<u32>) -> Option<u32> {
            self.values
                .range((Bound::Unbounded, x.as_ref()))
                .next_back()
                .copied()
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
    impl From<Range<u32>> for NumberSet {
        fn from(range: Range<u32>) -> NumberSet {
            NumberSet {
                sum: sum_range(range.clone()),
                values: range.collect(),
            }
        }
    }
    impl From<RangeInclusive<u32>> for NumberSet {
        fn from(range: RangeInclusive<u32>) -> NumberSet {
            NumberSet {
                sum: sum_range(range.clone()),
                values: range.collect(),
            }
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
mod tests {
    use super::*;

    struct TestCase {
        n: u32,
        expect_success: bool,
    }
    impl TestCase {
        #[inline]
        fn range(&self) -> RangeInclusive<u32> {
            1..=self.n
        }
        #[track_caller]
        fn verify_res(&self, res: Option<(NumberSet, NumberSet)>) {
            match self.try_verify_res(res) {
                Ok(()) => {}
                Err(error) => panic!("{error}"),
            }
        }
        #[allow(clippy::format_push_string, clippy::needless_pass_by_value)]
        fn try_verify_res(&self, res: Option<(NumberSet, NumberSet)>) -> Result<(), String> {
            let range = self.range();
            let expected_total_sum = sum_range(range.clone());
            let mut errors = Vec::new();
            // if we have a result, check the validity first
            if let Some((ref left, ref right)) = res {
                if left.sum() + right.sum() != expected_total_sum {
                    errors.push(format!(
                        "Expected sum(left) + sum(right) == sum({range:?}), but {sl} + {sr} != {st}",
                        sl = left.sum(),
                        sr = right.sum(),
                        st = expected_total_sum,
                    ));
                }
                if left.sum() != right.sum() {
                    errors.push(format!(
                        "Mismatched halves: sum(left) = {sl} != {sr} = sum(right)",
                        sl = left.sum(),
                        sr = right.sum(),
                    ));
                }
            }
            if self.expect_success {
                if !expected_total_sum.is_multiple_of(2) {
                    errors.push(format!(
                        "Expected to successfully split {range:?}, but the sum {expected_total_sum} is odd"
                    ));
                }
                if res.is_none() {
                    errors.push(format!(
                        "Expected to successfully split {range:?}, but got nothing"
                    ));
                }
            } else {
                if res.is_some() {
                    errors.push(format!(
                        "Expected failure to split {range:?}, but got a result anyways"
                    ));
                }
            }
            if errors.is_empty() {
                Ok(())
            } else {
                let range = self.range();
                let mut combined_message = format!(
                    "Failed test case for {range:?} with sum {st}:",
                    st = sum_range(self.range()),
                );
                for err in &errors {
                    combined_message.push_str("\n- ");
                    combined_message.push_str(err);
                }
                if let Some((ref left, ref right)) = res {
                    combined_message.push_str(&format!("\nLeft: {left:?}"));
                    combined_message.push_str(&format!("\nRight: {right:?}"));
                } else {
                    combined_message.push_str("\nResult: <missing>");
                }
                Err(combined_message)
            }
        }
    }
    const BASIC_TEST_CASES: &[TestCase] = &[
        TestCase {
            n: 7,
            expect_success: true,
        },
        TestCase {
            n: 6,
            expect_success: false,
        },
        TestCase {
            n: 1,
            expect_success: false,
        },
    ];

    #[test]
    fn naive_basic() {
        for case in BASIC_TEST_CASES {
            case.verify_res(naive_split(case.range()));
        }
    }

    #[test]
    fn intelligent_basic() {
        for case in BASIC_TEST_CASES {
            case.verify_res(intelligent_split(case.range()));
        }
    }

    const SLOW: &[TestCase] = &[
        // official test case 11
        TestCase {
            n: 26560,
            expect_success: true,
        },
        // official test 12
        TestCase {
            n: 155974,
            expect_success: false,
        },
        // official test 14
        TestCase {
            n: 260443,
            expect_success: true,
        },
        // official test 15
        TestCase {
            n: 275717,
            expect_success: false,
        },
        // official test 18
        TestCase {
            n: 653620,
            expect_success: true,
        },
    ];

    #[test]
    fn slow_intelligent() {
        for case in SLOW {
            intelligent_split(case.range());
        }
    }

    #[test]
    fn timeout_intelligent_max_input() {
        intelligent_split(1..=super::MAX_INPUT);
    }
}
