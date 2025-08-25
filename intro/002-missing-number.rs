#![allow(
    // already submitted
    clippy::redundant_closure_for_method_calls,
    clippy::stable_sort_primitive,
)]

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let mut lines = input.lines();
    let n = lines.next().unwrap().trim().parse::<u64>()?;
    let numbers = lines
        .next()
        .unwrap()
        .split_whitespace()
        .map(|x| x.parse::<u64>())
        .collect::<Result<Vec<_>, _>>()?;
    assert_eq!(lines.next(), None);
    println!("{}", find_missing_numbers(n, &numbers));
    Ok(())
}

fn find_missing_numbers(n: u64, nums: &[u64]) -> u64 {
    let mut sorted_nums = Vec::from(nums);
    sorted_nums.sort();
    for (index, &actual) in sorted_nums.iter().enumerate() {
        let expected = (index + 1) as u64;
        if expected != actual {
            return expected;
        }
    }
    if (sorted_nums.len() as u64) < n {
        sorted_nums.len() as u64 + 1
    } else {
        panic!("all {n} numbers present")
    }
}

#[cfg(test)]
mod test {
    use super::find_missing_numbers;

    #[test]
    fn example() {
        assert_eq!(find_missing_numbers(5, &[2, 3, 1, 5]), 4);
    }

    #[test]
    fn insufficient_entries() {
        assert_eq!(find_missing_numbers(5, &[1, 2, 3, 4]), 5);
    }

    #[test]
    #[should_panic = "all 5 numbers present"]
    fn all_entries() {
        find_missing_numbers(5, &[1, 2, 3, 4, 5]);
    }
}
