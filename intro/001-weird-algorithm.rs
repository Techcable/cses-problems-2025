fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let input = input.trim().parse::<u64>()?;
    weird_algorithm(input, |x| println!("{x}"));
    Ok(())
}

#[inline]
fn is_even(x: u64) -> bool {
    x & 1 == 0
}

pub fn weird_algorithm(mut x: u64, mut output: impl FnMut(u64)) {
    loop {
        output(x);
        if x == 1 {
            break;
        } else if is_even(x) {
            x >>= 1;
        } else {
            x *= 3;
            x += 1;
        }
    }
}

#[cfg(test)]
mod test {
    #![allow(clippy::pedantic, clippy::all)] // already submitted & written before clippy was run with --tests
    use super::weird_algorithm;

    fn weird_algorithm_vec(x: u64) -> Vec<u64> {
        let mut res = Vec::new();
        weird_algorithm(x, |x| res.push(x));
        res
    }

    #[test]
    fn example() {
        assert_eq!(weird_algorithm_vec(3), vec![3, 10, 5, 16, 8, 4, 2, 1]);
    }
}
