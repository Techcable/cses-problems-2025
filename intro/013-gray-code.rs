use crate::bitstring::SmallBitString;
use std::fmt;
use std::fmt::{Debug, Display, Formatter};
use std::ops::Deref;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let input = input.trim().parse::<u32>()?;
    for x in problem(input) {
        println!("{x}");
    }
    Ok(())
}

const ZERO: bool = false;
const ONE: bool = true;

pub const MAX_INPUT: u32 = 16;

pub fn problem(n: u32) -> GreyCode {
    generate_grey_code(n)
}

/// Builds a gray code for a fixed length `n`.
///
/// For `n=2`, produces the following output:
/// ```
/// 00
/// 01
/// 11
/// 10
/// ```
///
/// In general, for length `n`,
/// the first item is all zeroes and the last item has just a single one in the most significant bit.
/// This allows us to recursively generate the grey code for any length in the following matter:
/// grey_code(n-1).map(|x| x.prepend(0)).chain(grey_code(n-1)
///
fn generate_grey_code(n: u32) -> GreyCode {
    assert!(n > 0);
    if n == 1 {
        return GreyCode(vec![SmallBitString::from(ZERO), SmallBitString::from(ONE)]);
    }
    let mut res = Vec::with_capacity(2usize.pow(n));
    let inner = generate_grey_code(n - 1);
    debug_assert_eq!(
        inner.first().copied(),
        Some(SmallBitString::zeroes(n as usize - 1)),
    );
    debug_assert_eq!(
        inner.last().copied(),
        Some(SmallBitString::from(ONE) << (n - 2))
    );
    for mut short in inner.iter().copied() {
        short.push(ZERO); // MSB is zero
        res.push(short);
    }
    for mut short in inner.iter().rev().copied() {
        short.push(ONE); // MSB is one
        res.push(short);
    }
    GreyCode(res)
}
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct GreyCode(Vec<SmallBitString>);
impl Deref for GreyCode {
    type Target = [SmallBitString];
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<'a> IntoIterator for &'a GreyCode {
    type Item = SmallBitString;
    type IntoIter = std::iter::Copied<std::slice::Iter<'a, SmallBitString>>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter().copied()
    }
}
impl IntoIterator for GreyCode {
    type Item = SmallBitString;
    type IntoIter = std::vec::IntoIter<SmallBitString>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}
impl FromIterator<SmallBitString> for GreyCode {
    fn from_iter<T: IntoIterator<Item = SmallBitString>>(iter: T) -> Self {
        GreyCode(iter.into_iter().collect())
    }
}
impl Debug for GreyCode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        struct DebugAsDisplay(SmallBitString);
        impl Debug for DebugAsDisplay {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                Display::fmt(&self.0, f)
            }
        }
        f.debug_list()
            .entries(self.0.iter().copied().map(DebugAsDisplay))
            .finish()
    }
}
impl Display for GreyCode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{self:#?}")
    }
}

pub fn compute_hamming_distance(a: SmallBitString, b: SmallBitString) -> usize {
    assert_eq!(
        a.len(),
        b.len(),
        "hamming distance only defined for same-length strings"
    );
    let mut count = 0;
    for idx in 0..a.len() {
        count += usize::from(a[idx] != b[idx]);
    }
    count
}

#[cfg(test)]
mod test {
    use super::*;
    use std::collections::HashSet;

    #[track_caller]
    fn verify_grey_code(n: u32) -> GreyCode {
        let code = generate_grey_code(n);
        assert_eq!(
            code.len(),
            2usize.pow(n),
            "Grey code for n={n} has unexpected length: {code}",
        );
        let mut seen = HashSet::new();
        let mut iter = code.iter().copied();
        let mut last = iter.next().expect("empty grey code");
        seen.insert(last);
        for s in iter {
            assert!(
                seen.insert(s),
                "Multiple occurrences of element {s} in {code}",
            );
            assert_eq!(
                compute_hamming_distance(last, s),
                1,
                "dist({last}, {s}) != 1 for {code}",
            );
            last = s;
        }
        code
    }

    #[track_caller]
    fn known_grey_code<'a>(s: impl AsRef<[&'a str]>) -> GreyCode {
        s.as_ref().iter().copied().map(bitstring).collect()
    }

    #[track_caller]
    fn bitstring(s: &str) -> SmallBitString {
        s.parse().unwrap_or_else(|e| panic!("{e} (for {s:?})"))
    }

    #[test]
    fn example() {
        assert_eq!(
            verify_grey_code(2),
            known_grey_code(["00", "01", "11", "10"])
        );
    }

    #[test]
    fn length3() {
        assert_eq!(
            verify_grey_code(3),
            known_grey_code(["000", "001", "011", "010", "110", "111", "101", "100",])
        );
    }
}

mod bitstring {
    use std::fmt::{Debug, Display, Formatter, Write};
    use std::iter::FusedIterator;
    use std::ops::{Index, Shl};
    use std::str::FromStr;

    /// A bit string limited to [`Self::CAPACITY`] elements.
    ///
    /// Elements with higher index have more significance.
    #[derive(Copy, Clone, Eq, PartialEq, Hash, Default)]
    pub struct SmallBitString {
        /// The actual storage for the string.
        ///
        /// In order for `derive(Eq, Hash)` to work, bits beyond `len` should be zero.
        bits: u64,
        len: u8,
    }
    impl SmallBitString {
        pub const CAPACITY: usize = u64::BITS as usize;

        #[inline]
        #[allow(clippy::cast_possible_truncation)] // overflow impossible due to capacity check
        pub const fn zeroes(len: usize) -> SmallBitString {
            assert!(len <= Self::CAPACITY);
            SmallBitString {
                len: len as u8,
                bits: 0,
            }
        }

        #[inline]
        #[allow(clippy::cast_possible_truncation)] // overflow impossible due to capacity check
        pub const fn ones(len: usize) -> SmallBitString {
            assert!(len <= Self::CAPACITY);
            SmallBitString {
                len: len as u8,
                bits: (1 << len) - 1,
            }
        }

        #[inline]
        pub fn is_empty(&self) -> bool {
            self.len == 0
        }

        #[inline]
        pub fn len(&self) -> usize {
            self.len as usize
        }

        pub const fn new() -> SmallBitString {
            SmallBitString { bits: 0, len: 0 }
        }

        #[track_caller]
        pub fn push(&mut self, b: bool) {
            assert!(self.len() < Self::CAPACITY, "capacity overflow");
            if b {
                self.bits |= 1u64 << self.len();
            }
            self.len += 1;
        }

        pub fn pop(&mut self) -> Option<bool> {
            if self.is_empty() {
                None
            } else {
                let res = self[self.len() - 1];
                self.set(self.len() - 1, false);
                self.len -= 1;
                Some(res)
            }
        }

        #[inline]
        pub fn get(&self, idx: usize) -> Option<bool> {
            if idx < self.len() {
                Some((self.bits & (1u64 << idx)) != 0)
            } else {
                None
            }
        }

        #[track_caller]
        pub fn set(&mut self, idx: usize, b: bool) {
            assert!(idx < self.len(), "index out of bounds");
            let mask = 1u64 << idx;
            if b {
                self.bits |= mask;
            } else {
                self.bits &= !mask;
            }
        }

        #[inline]
        pub fn iter(&self) -> Iter {
            Iter { s: *self, idx: 0 }
        }
        #[inline]
        pub fn chars(&self) -> impl DoubleEndedIterator<Item = char> + ExactSizeIterator {
            self.iter().map(bit_to_char)
        }
    }
    impl Shl<u32> for SmallBitString {
        type Output = SmallBitString;

        #[track_caller]
        #[allow(clippy::cast_possible_truncation)] // overflow impossible due to capacity check
        fn shl(mut self, rhs: u32) -> Self::Output {
            let new_len = (self.len as u32).saturating_add(rhs);
            assert!(
                new_len as usize <= Self::CAPACITY,
                "shifting a string of length {} by {rhs} would overflow capacity",
                self.len()
            );
            self.len += rhs as u8;
            self.bits <<= rhs;
            self
        }
    }
    impl From<bool> for SmallBitString {
        fn from(value: bool) -> Self {
            let mut res = SmallBitString::new();
            res.push(value);
            res
        }
    }
    impl FromStr for SmallBitString {
        type Err = InvalidCharError;

        fn from_str(s: &str) -> Result<SmallBitString, InvalidCharError> {
            s.chars().rev().map(char_to_bit).collect()
        }
    }
    /// Get the character corresponding to the specified bit.
    #[inline]
    pub fn bit_to_char(c: bool) -> char {
        if c {
            '1'
        } else {
            '0'
        }
    }
    /// Get the bit corresponding to the specified character.
    #[inline]
    pub fn char_to_bit(c: char) -> Result<bool, InvalidCharError> {
        match c {
            '1' => Ok(true),
            '0' => Ok(false),
            _ => Err(InvalidCharError(c)),
        }
    }
    #[derive(Debug, Clone)]
    pub struct InvalidCharError(char);
    impl Display for InvalidCharError {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            write!(f, "Invalid bit {:?} must be '1' or '0'", self.0)
        }
    }
    impl Display for SmallBitString {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            for c in self.chars().rev() {
                f.write_char(c)?;
            }
            Ok(())
        }
    }
    impl Debug for SmallBitString {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            write!(f, "SmallBitString({self})")
        }
    }
    impl From<SmallBitString> for String {
        fn from(value: SmallBitString) -> Self {
            value.chars().collect()
        }
    }
    impl IntoIterator for SmallBitString {
        type Item = bool;
        type IntoIter = Iter;
        fn into_iter(self) -> Iter {
            self.iter()
        }
    }
    impl IntoIterator for &SmallBitString {
        type Item = bool;
        type IntoIter = Iter;
        #[inline]
        fn into_iter(self) -> Iter {
            self.iter()
        }
    }
    #[derive(Clone, Eq, PartialEq, Hash)]
    pub struct Iter {
        idx: u8,
        s: SmallBitString,
    }
    impl Iterator for Iter {
        type Item = bool;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            if self.idx < self.s.len {
                let item = self.s[self.idx as usize];
                self.idx += 1;
                Some(item)
            } else {
                None
            }
        }

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            let len = (self.s.len - self.idx) as usize;
            (len, Some(len))
        }
    }
    impl DoubleEndedIterator for Iter {
        #[inline]
        fn next_back(&mut self) -> Option<bool> {
            self.s.pop()
        }
    }
    impl ExactSizeIterator for Iter {}
    impl FusedIterator for Iter {}
    impl Index<usize> for SmallBitString {
        type Output = bool;
        #[inline]
        #[track_caller]
        fn index(&self, index: usize) -> &Self::Output {
            const TRUE: &bool = &true;
            const FALSE: &bool = &false;
            match self.get(index) {
                Some(true) => TRUE,
                Some(false) => FALSE,
                None => panic!(
                    "index {index} out of bounds for len {len}",
                    len = self.len()
                ),
            }
        }
    }
    impl Index<u32> for SmallBitString {
        type Output = bool;
        #[inline]
        #[track_caller]
        fn index(&self, index: u32) -> &Self::Output {
            &self[index as usize]
        }
    }
    impl FromIterator<bool> for SmallBitString {
        fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
            let mut res = SmallBitString::new();
            for value in iter {
                res.push(value);
            }
            res
        }
    }
}
