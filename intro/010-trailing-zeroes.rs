//! Computes the number of trailing zeroes in `n!`.
//!
//! This is equal to the number of times a factor of 10 appears in `n!`.
//! So either a multiple of 10 appears in the expansion of `n!`,
//! or a multiple of 5 along with a multiple of 2.

use std::ops::{RangeInclusive, RangeToInclusive};

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let input = input.trim().parse::<u32>()?;
    println!("{}", problem(input));
    Ok(())
}

pub const MAX_INPUT: u32 = 10u32.pow(9);

fn problem(n: u32) -> u64 {
    let factors_of_10 = count_factors_with_multiplicity(..=n, 10);
    let factors_of_5 = count_factors_with_multiplicity(..=n, 5) - factors_of_10;
    let factors_of_2 = count_factors_with_multiplicity(..=n, 2) - factors_of_10;
    factors_of_10 + factors_of_5.min(factors_of_2)
}

/// This algorithm runs in `log(range.end)` time.
fn count_factors_with_multiplicity(range: RangeToInclusive<u32>, factor: u32) -> u64 {
    if range.end < factor {
        return 0;
    }
    let max_power = range.end.ilog(factor);
    debug_assert!(
        (factor as u64).pow(max_power + 1) >= range.end as u64,
        "{factor}^{max_power} is not maximum power of {range:?}"
    );
    let mut count: u64 = 0;
    for power in 1..=max_power {
        let value = factor.pow(power);
        // we are only counting the additional factors added by consideration of `value`
        count += range_step_len(value..=range.end, value) as u64;
    }
    count
}

/// Calculates `range.step_by(step).count()` in O(1) time.
#[inline]
fn range_step_len(range: RangeInclusive<u32>, step: u32) -> u32 {
    assert_ne!(step, 0);
    let len = (range.end() - range.start()) + 1;
    let elements_after_start = (len - 1) / step;
    elements_after_start + 1
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn range_step_len() {
        #[track_caller]
        fn verify(x: RangeInclusive<u32>, step: u32) {
            assert_eq!(
                super::range_step_len(x.clone(), step) as usize,
                x.clone().step_by(step as usize).count(),
                "Unexpected length for {x:?}.step_by({step})"
            );
        }
        verify(0..=2, 2);
        verify(0..=20, 5);
        verify(0..=19, 5);
        verify(7..=18, 2);
        verify(10..=100, 3);
        verify(0..=97, 7);
        verify(0..=95, 7);
        verify(0..=101, 7);
    }

    #[test]
    fn example() {
        assert_eq!(problem(20), 4);
    }

    #[test]
    fn timeout_max_input() {
        let _ = problem(MAX_INPUT);
    }

    #[test]
    fn official_tests() {
        assert_eq!(problem(395), 97); // test1
        assert_eq!(problem(850915850), 212728957); // test2
        assert_eq!(problem(871), 215); // test3
        assert_eq!(problem(239), 57); // test4
        assert_eq!(problem(850915850), 212728957); // test8
        assert_eq!(problem(19273478), 4818363); // test9
        assert_eq!(problem(669763357), 167440831); // test10
    }
}
