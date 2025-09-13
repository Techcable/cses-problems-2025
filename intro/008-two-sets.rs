use crate::set::NumberSet;
use std::cmp::Ordering;
use std::ops::ControlFlow;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let input = input.trim().parse::<u32>()?;
    let mut left = (1..=input).collect::<NumberSet>();
    let orig_sum = left.sum();
    let mut right = NumberSet::new();
    fn print_set(x: &NumberSet) {
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
    let res = naive_search(&mut left, &mut right, &mut move |left, right| {
        assert_eq!(left.sum() + right.sum(), orig_sum);
        println!("YES");
        print_set(left);
        print_set(right);
        ControlFlow::Break(())
    });
    if res.is_continue() {
        println!("NO");
    }
    Ok(())
}

type SuccessCallback = dyn FnMut(&NumberSet, &NumberSet) -> ControlFlow<()>;

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

pub const MAX_INPUT: u32 = 10u32.pow(6);

mod set {
    //! Defines the [`NumberSet`] type.
    //!
    //! This is in its own module for better encapsulation.
    use std::collections::{btree_set, BTreeSet};
    use std::ops::{Bound, RangeInclusive};

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
