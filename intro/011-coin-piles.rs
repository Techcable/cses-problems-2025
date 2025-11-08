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
pub fn problem(a: u32, b: u32) -> bool {
    if a > b {
        return problem(b, a);
    }
    assert!(a <= b);
    // if they are equal, we can only handle multiples of two
    if a == b {
        return a % 3 == 0;
    }
    if a == 0 {
        return false;
    }
    let excess = b - a;
    // the only possible way to get rid of the excess in `b` is to subtract 2 for b,
    // then one from a
    a >= excess && problem(a - excess, b - (excess * 2))
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

    #[test]
    fn test1_small_failures() {
        #[track_caller]
        fn require_yes(a: u32, b: u32) {
            assert!(
                problem(a, b),
                "problem({a}, {b}) should be `YES` (naive_problem is {})",
                if naive_problem(a, b) { "YES" } else { "NO" }
            );
        }
        require_yes(22, 41);
        require_yes(19, 35);
        require_yes(19, 38);
        require_yes(18, 36);
        require_yes(17, 34);
    }
}
