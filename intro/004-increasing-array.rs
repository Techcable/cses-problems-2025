pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let numbers = input
        .split_whitespace()
        .map(|x| x.parse::<u64>())
        .collect::<Result<Vec<_>, _>>()?;
    println!("{}", moves_needed(&numbers));
    Ok(())
}

fn moves_needed(nums: &[u64]) -> u64 {
    let mut moves = 0;
    let mut iter = nums.iter();
    let mut last = iter.next().unwrap();
    for x in iter {
        if x < last {
            moves += last - x;
        }
        last = x;
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
}
