use std::cmp::Ordering;
use std::str::FromStr;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let mut lines = input.lines();
    let num_inputs = lines.next().unwrap().trim().parse::<usize>()?;
    let inputs = lines
        .map(|line| {
            let entries = line
                .split_whitespace()
                .map(u32::from_str)
                .collect::<Result<Vec<_>, _>>()?;
            assert_eq!(entries.len(), 2);
            Ok((entries[0], entries[1]))
        })
        .collect::<Result<Vec<_>, Box<dyn std::error::Error>>>()?;
    assert_eq!(inputs.len(), num_inputs);
    for (a, b) in inputs {
        println!("{}", if problem(a, b) { "YES" } else { "NO" });
    }
    Ok(())
}

pub const MAX_INPUT: u32 = 10u32.pow(9);
const SMALL_INPUT_BOUND: u32 = 16;
pub fn problem(a: u32, b: u32) -> bool {
    // slash problem size before using dynamic programming
    // this works because we can always reduce both inputs by 3 by doing a - 1 - 2, b - 2 - 1
    //
    // after this reduction, min(a, b) <= SMALL_INPUT_BOUND
    let (a, b) = if a > SMALL_INPUT_BOUND && b > SMALL_INPUT_BOUND {
        let to_trim = a.min(b) - SMALL_INPUT_BOUND;
        // Must be careful to round up to the nearest multiple of 3 rather than down,
        // otherwise it is possible one input will not get quite below the bound
        let to_trim = to_trim + (3 - (to_trim % 3));
        debug_assert_eq!(to_trim % 3, 0);
        (a - to_trim, b - to_trim)
    } else {
        (a, b)
    };
    assert!(a.min(b) <= SMALL_INPUT_BOUND, "({a}, {b})");
    // Impossible to succeed when one input is more than double another
    // that is because the most aggressively we can take from `a` is -2, -1 each time.
    // On the other hand, we are guaranteed to succeed when one input is exactly another
    //
    // After this reduction, max(a, b) < 2 * min(a, b) < 2 * SMALL_INPUT_BOUND
    let min_input = a.min(b);
    let max_input = a.max(b);
    match max_input.cmp(&(min_input * 2)) {
        Ordering::Greater => return false,
        Ordering::Equal => return true,
        Ordering::Less => {} // continue
    }
    assert!(max_input < SMALL_INPUT_BOUND * 2, "({a}, {b})");
    naive_problem(a, b)
}

pub fn naive_problem(a: u32, b: u32) -> bool {
    do_search(a, b, naive_problem)
}
#[inline]
fn do_search(a: u32, b: u32, subproblem: impl Fn(u32, u32) -> bool) -> bool {
    if a == 0 || b == 0 {
        a == 0 && b == 0
    } else {
        (a > 1 && subproblem(a - 2, b - 1)) || (b > 1 && subproblem(a - 1, b - 2))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::u32::MAX;

    #[test]
    fn naive_example() {
        assert!(naive_problem(2, 1));
        assert!(!naive_problem(2, 2));
        assert!(naive_problem(3, 3));
    }

    #[test]
    fn example() {
        assert!(problem(2, 1));
        assert!(!problem(2, 2));
        assert!(problem(3, 3));
    }

    #[test]
    fn timeout_max_input() {
        let _ = problem(MAX_INPUT, MAX_INPUT);
    }
}
