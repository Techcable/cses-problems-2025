/// Thanks to the python builtin bignum implementation,
/// this has a one-line python solution.
/// See `009-bit-strings.py` for details.
/// Ironically, this rust impl is probably slower than the python impl.
pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let input = input.trim().parse::<u32>()?;
    println!("{}", problem(input));
    Ok(())
}

fn problem(x: u32) -> u32 {
    assert_ne!(x, 0, "zero is forbidden by problem statement");
    pow_mod::<PROBLEM_MODULUS>(2, x)
}
/// The fact this is a constant is important,
/// because it reduces a division operation to shift+add.
const PROBLEM_MODULUS: u32 = 10u32.pow(9) + 7;

#[inline] // want modulo reduced to shift+add when constant
#[allow(clippy::cast_possible_truncation)] // not possible since modulo is u32
fn mul_mod(a: u32, b: u32, modulo: u32) -> u32 {
    (u64::from(a).wrapping_mul(b as u64) % (modulo as u64)) as u32
}

/// Exponentiation by squaring, modulo [`MODULUS`].
///
/// Code based off the implementation in [`u32::pow`].
fn pow_mod<const MODULUS: u32>(mut base: u32, mut exp: u32) -> u32 {
    if exp == 0 {
        return 1;
    }
    let mut acc = 1;
    loop {
        if (exp & 1) == 1 {
            acc = mul_mod(acc, base, MODULUS);
            // since exp!=0, finally the exp must be 1.
            if exp == 1 {
                return acc;
            }
        }
        exp /= 2;
        base = mul_mod(base, base, MODULUS);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn example1() {
        assert_eq!(problem(3), 8);
    }

    #[test]
    fn test1() {
        // official test
        assert_eq!(problem(7), 128);
    }

    #[test]
    fn test5() {
        assert_eq!(problem(447), 941778035);
    }
}
