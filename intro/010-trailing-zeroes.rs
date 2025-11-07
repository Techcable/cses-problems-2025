//! Computes the number of trailing zeroes in `n!`.
//!
//! This is equal to the number of times a factor of 10 appears in `n!`.
//! So either a multiple of 10 appears in the expansion of `n!`,
//! or a multiple of 5 along with a multiple of 2.

use std::ops::Range;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let input = input.trim().parse::<u32>()?;
    println!("{}", problem(input));
    Ok(())
}

fn problem(n: u32) -> u64 {
    let range = || 1..(n + 1);
    let factors_of_10 = sum_range_step(range(), 10) / 10;
    let factors_of_5 = sum_range_step(range(), 5) / 5;
    let factors_of_2 = sum_range_step(range(), 2) / 2;
    factors_of_10 + factors_of_5.min(factors_of_2)
}

//
// range math
//

/// Sum all the values in the specified range, stepping by a certain amount.
#[inline]
pub fn sum_range_step(orig: Range<u32>, step: u32) -> u64 {
    // The following observation tells us how to reduce step>1 to step=1:
    //   sum_range_step(0..=21, 5) = 0 + 5 + 10 + 15 + 20 = 5(0 + 1 + 2 + 3 + 4)
    // This shows us how to deal with non-zero start:
    //   sum_range_step(6..20, 5) = 6 + 11 + 16 = (6 * 3) + 5(0 + 1 + 2)
    //
    // Now all together:
    assert_ne!(step, 0);
    let orig_len = orig.end - orig.start;
    let len = ((orig_len - 1) / step) // elements after start
        + 1; // start element
    debug_assert_eq!(
        orig.clone().step_by(step as usize).len() as u64,
        len as u64,
        "{orig:?}.step_by({step}), values = {:?}, orig_len = {orig_len}",
        orig.clone().step_by(step as usize).collect::<Vec<u32>>()
    );
    (len as u64 * orig.start as u64) + (sum_range(0..len) * (step as u64))
}

/// Sum all the values in the specified range.
///
/// Equivalent to `range.sum()` but takes O(1) time.
#[inline]
pub fn sum_range(range: Range<u32>) -> u64 {
    let len = (range.end - range.start) as u64;
    // special-case is needed to avoid integer underflow
    if len == 0 {
        0
    } else {
        (len * range.start as u64) + ((len * (len - 1)) / 2)
    }
}

#[inline] // want modulo reduced to shift+add when constant
#[allow(clippy::cast_possible_truncation)] // not possible since modulo is u32
pub fn mul_mod(a: u32, b: u32, modulo: u32) -> u32 {
    (u64::from(a).wrapping_mul(b as u64) % (modulo as u64)) as u32
}

#[cfg(test)]
mod test {
    use super::*;
    use std::ops::Range;

    #[test]
    fn sum_range_step_verify() {
        #[track_caller]
        fn verify(x: Range<u32>, step: u32) {
            assert_eq!(
                super::sum_range_step(x.clone(), step),
                x.clone().step_by(step as usize).map(u64::from).sum::<u64>(),
                "Unexpected sum for {x:?}.step_by({step})"
            );
        }
        verify(0..20, 5);
        verify(7..18, 2);
        verify(10..100, 3);
        verify(0..97, 7);
        verify(0..95, 7);
        verify(0..101, 7);
    }

    #[test]
    fn example() {
        assert_eq!(problem(20), 4);
    }
}
