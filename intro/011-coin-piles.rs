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
const SMALL_INPUT_BOUND: u32 = 6;
pub fn problem(a: u32, b: u32) -> bool {
    fn small_problem(a: u32, b: u32) -> bool {
        if a / 2 > b || b / 2 > a {
            false
        } else {
            do_search(a, b, small_problem)
        }
    }
    // slash problem size before using dynamic programming
    // this works because we can always reduce both inputs by 3 by doing a - 1 - 2, b - 2 - 1
    //
    // after this reduction, the runtime is O(MAX_INPUT^2) ~ O(1)
    if a >= SMALL_INPUT_BOUND && b >= SMALL_INPUT_BOUND {
        let to_trim = a.min(b) - SMALL_INPUT_BOUND;
        let to_trim = to_trim - (to_trim % 3);
        debug_assert!(to_trim.is_multiple_of(3));
        small_problem(a - to_trim, b - to_trim)
    } else {
        small_problem(a, b)
    }
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
