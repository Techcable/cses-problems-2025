pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let mut lines = input.lines();
    let n = lines.next().unwrap().trim().parse::<usize>()?;
    let numbers = lines
        .next()
        .unwrap()
        .split_whitespace()
        .map(|x| x.parse::<u64>())
        .collect::<Result<Vec<_>, _>>()?;
    assert_eq!(numbers.len(), n);
    println!("{}", moves_needed(&numbers));
    Ok(())
}

fn moves_needed(nums: &[u64]) -> u64 {
    let mut moves = 0;
    let mut iter = nums.iter();
    let mut lower_bound = iter.next().unwrap();
    for x in iter {
        if x < lower_bound {
            moves += lower_bound - x;
        } else {
            lower_bound = x;
        }
    }
    moves
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn example() {
        assert_eq!(moves_needed(&[3, 2, 5, 1, 7]), 5);
    }

    #[test]
    fn official_1() {
        assert_eq!(moves_needed(&[1, 1, 1, 1, 1, 1, 1, 1, 1, 1]), 0);
    }

    #[test]
    fn official_2() {
        assert_eq!(
            moves_needed(&[1000000000, 1, 1, 1, 1, 1, 1, 1, 1, 1,]),
            8999999991
        );
    }

    #[test]
    fn official_3() {
        assert_eq!(moves_needed(&[6, 10, 4, 10, 2, 8, 9, 2, 7, 7]), 31);
    }
}
