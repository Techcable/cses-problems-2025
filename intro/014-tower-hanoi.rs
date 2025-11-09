use std::fmt::{Debug, Display, Formatter};

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let input = input.trim().parse::<u32>()?;
    let result = problem(input);
    println!("{}", result.len());
    for &x in &result {
        println!("{}", x.cses_output());
    }
    Ok(())
}

pub fn problem(n: u32) -> Vec<Action> {
    let mut actions = Vec::new();
    do_movement(Stack::Left, Stack::Right, Stack::Middle, n, &mut actions);
    actions
}

/// Move all elements from the source stack to the dest stack.
///
/// Assumes that the
fn do_movement(src: Stack, dest: Stack, scratch: Stack, size: u32, actions: &mut Vec<Action>) {
    assert_ne!(src, dest);
    assert_ne!(scratch, src);
    assert_ne!(scratch, dest);
    if size == 1 {
        // only need a single action
        actions.push(Action { src, dest });
        return;
    }
    do_movement(src, scratch, dest, size - 1, actions);
    actions.push(Action { src, dest });
    do_movement(scratch, dest, src, size - 1, actions);
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Stack {
    Left,
    Middle,
    Right,
}
impl Stack {
    pub const ALL: [Stack; 3] = [Stack::Left, Stack::Middle, Stack::Right];
    #[track_caller]
    pub fn from_index(index: usize) -> Stack {
        match index {
            0 => Stack::Left,
            1 => Stack::Middle,
            2 => Stack::Right,
            _ => panic!("Invalid index {index}"),
        }
    }
}
impl Display for Stack {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Stack::Left => f.write_str("left"),
            Stack::Middle => f.write_str("middle"),
            Stack::Right => f.write_str("right"),
        }
    }
}
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Action {
    pub src: Stack,
    pub dest: Stack,
}
impl Action {
    pub fn reverse(&self) -> Action {
        Action {
            dest: self.src,
            src: self.dest,
        }
    }
    /// Format this action in the way expected by CSES.
    pub fn cses_output(&self) -> impl Display {
        struct CsesFormat(Action);
        impl Display for CsesFormat {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                write!(
                    f,
                    "{} {}",
                    self.0.src as usize + 1,
                    self.0.dest as usize + 1
                )
            }
        }
        CsesFormat(*self)
    }
}
impl Display for Action {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} to {}", self.src, self.dest)
    }
}
impl Debug for Action {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Action")
            .field(&self.src)
            .field(&self.dest)
            .finish()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    const EXAMPLE_ACTIONS: [Action; 3] = [
        Action {
            src: Stack::Left,
            dest: Stack::Middle,
        },
        Action {
            src: Stack::Left,
            dest: Stack::Right,
        },
        Action {
            src: Stack::Middle,
            dest: Stack::Right,
        },
    ];

    fn actions(s: &[(u32, u32)]) -> Vec<Action> {
        s.iter()
            .map(|&(a, b)| Action {
                src: Stack::from_index(a as usize - 1),
                dest: Stack::from_index(b as usize - 1),
            })
            .collect()
    }

    #[test]
    fn size3() {
        assert_eq!(
            problem(3),
            actions(&[(1, 3), (1, 2), (3, 2), (1, 3), (2, 1), (2, 3), (1, 3),])
        );
    }

    #[test]
    fn example_naive() {
        assert_eq!(problem(2), EXAMPLE_ACTIONS.to_vec());
    }
}
