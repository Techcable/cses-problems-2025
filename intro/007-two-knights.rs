use std::sync::OnceLock;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let input = input.trim().parse::<u32>()?;
    for x in 1..=input {
        println!("{}", count_possible_placements(BoardSize(x)));
    }
    // just used to ensure nothing overflows a u32
    let _ = MAX_BOARD_SPACES;
    Ok(())
}

const MAX_INPUT: u32 = 10_000;
const MAX_BOARD_SPACES: u32 = MAX_INPUT * MAX_INPUT;

#[derive(Copy, Clone, Debug)]
pub struct BoardSize(pub u32);
impl BoardSize {
    fn all_positions(self) -> impl Iterator<Item = Position> + 'static {
        Position { row: 0, column: 0 }.remaining_positions(self)
    }
    #[inline]
    pub fn count_spaces(&self) -> u32 {
        self.0 * self.0
    }
}

#[derive(Copy, Clone, Debug, Ord, Eq, PartialOrd, PartialEq)]
pub struct Position {
    row: u32,
    column: u32,
}
impl Position {
    #[inline]
    fn remaining_positions(self, size: BoardSize) -> impl Iterator<Item = Position> + 'static {
        std::iter::successors(Some(self), move |x| x.next(size))
    }
    #[inline]
    pub fn next(self, size: BoardSize) -> Option<Position> {
        debug_assert!(self.column < size.0);
        debug_assert!(self.row < size.0);
        if self.column + 1 < size.0 {
            Some(Position {
                column: self.column + 1,
                ..self
            })
        } else if self.row + 1 < size.0 {
            Some(Position {
                column: 0,
                row: self.row + 1,
            })
        } else {
            None
        }
    }
    #[inline]
    pub fn checked_offset(self, offset: Offset, size: BoardSize) -> Option<Position> {
        Some(Position {
            row: self
                .row
                .checked_add_signed(offset.row)
                .filter(|&x| x < size.0)?,
            column: self
                .column
                .checked_add_signed(offset.column)
                .filter(|&x| x < size.0)?,
        })
    }
}
#[derive(Copy, Clone, Debug)]
pub struct Offset {
    row: i32,
    column: i32,
}

static KNIGHT_MOVEMENTS: OnceLock<[Offset; 8]> = OnceLock::new();
fn knight_movements() -> &'static [Offset; 8] {
    KNIGHT_MOVEMENTS.get_or_init(|| {
        let mut res = [Offset { row: 0, column: 0 }; 8];
        let mut idx = 0;
        for row_magnitude in [1, 2] {
            let col_magnitude = 3 - row_magnitude;
            for row_dir in [-1, 1] {
                for col_dir in [-1, 1] {
                    res[idx] = Offset {
                        row: row_magnitude * row_dir,
                        column: col_magnitude * col_dir,
                    };
                    idx += 1;
                }
            }
        }
        assert!(idx == res.len());
        res
    })
}

pub fn count_possible_placements(size: BoardSize) -> u64 {
    let spaces = size.count_spaces();
    let mut total = 0u64;
    let movements = knight_movements();
    // there is symmetry here: Knight A can attack knight B iff B can attack knight B
    // So after placing knight A, then B can be wherever A does not attack
    //
    // In order to avoid double counting, we only count positions >= knight,
    // taking advantage of the total order of Position and the fact the iterator
    // respects that ordering
    for (index, knight) in size.all_positions().enumerate() {
        let mut this_board_combos = spaces - 1 - u32::try_from(index).unwrap();
        for &movement in movements {
            if let Some(pos) = knight.checked_offset(movement, size) {
                if pos > knight {
                    this_board_combos -= 1;
                }
            }
        }
        total += this_board_combos as u64;
    }
    total
}

#[cfg(test)]
mod test {
    use super::{count_possible_placements, BoardSize};
    #[test]
    fn example() {
        const EXAMPLE_EXPECTED: &[u64] = &[0, 6, 28, 96, 252, 550, 1056, 1848];
        for (index, &expected) in EXAMPLE_EXPECTED.iter().enumerate() {
            let size = BoardSize(index as u32 + 1);
            assert_eq!(count_possible_placements(size), expected, "{size:?}");
        }
    }

    #[test]
    fn iter_order() {
        let size = BoardSize(5);
        let mut prev_seen = Vec::new();
        for x in size.all_positions() {
            for &y in &prev_seen {
                assert!(y < x);
            }
            for y in x.remaining_positions(size) {
                assert!(y >= x, "{y:?} < {x:?}")
            }
            prev_seen.push(x);
        }
    }
}
