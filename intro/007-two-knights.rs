use std::cmp::Ordering;
use std::sync::OnceLock;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let input = input.trim().parse::<u32>()?;
    count_possible_placements(BoardSize(input), &mut |_size, total| {
        println!("{total}");
    });
    // just used to ensure nothing overflows a u32
    let _ = MAX_BOARD_SPACES;
    Ok(())
}

const MAX_INPUT: u32 = 10_000;
const MAX_BOARD_SPACES: u32 = MAX_INPUT * MAX_INPUT;

#[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct BoardSize(pub u32);
impl BoardSize {
    fn all_positions(self) -> impl Iterator<Item = Position> + 'static {
        Position { row: 0, column: 0 }.remaining_positions(self)
    }
    #[inline]
    pub fn available_spaces(&self) -> u32 {
        self.0 * self.0
    }
    #[inline]
    pub fn index(&self) -> u32 {
        self.0 - 1
    }
}

/// Spirals across the chess board:
///
/// Assume the following board with the top left at position (0, 0)
/// ```
/// A B
/// D C
/// ```
/// The iterator will give `[A, B, C, D]`
pub struct BoardSpiralIter {
    max_size: BoardSize,
    pos: Option<Position>,
}
impl Iterator for BoardSpiralIter {
    type Item = Position;
    fn next(&mut self) -> Option<Self::Item> {
        let old_pos = self.pos?;
        let current_size = old_pos.needed_size();
        let new_pos: Option<Position>;
        if old_pos.row < current_size.index() {
            new_pos = Some(Position {
                row: old_pos.row + 1,
                ..old_pos
            });
        } else if old_pos.column > 0 {
            new_pos = Some(Position {
                column: old_pos.column - 1,
                ..old_pos
            });
        } else if current_size < self.max_size {
            // start again at top right of new
            new_pos = Some(Position {
                row: 0,
                column: current_size.index() + 1,
            });
        } else {
            new_pos = None;
        }
        self.pos = new_pos;
        Some(old_pos)
    }
}
impl Ord for Position {
    fn cmp(&self, other: &Self) -> Ordering {
        self.needed_size().cmp(&other.needed_size()).then_with(|| {
            self.row
                .cmp(&other.row)
                .then(self.column.cmp(&other.column).reverse())
        })
    }
}
impl PartialOrd for Position {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Position {
    row: u32,
    column: u32,
}
impl Position {
    #[inline]
    fn remaining_positions(self, size: BoardSize) -> impl Iterator<Item = Position> + 'static {
        BoardSpiralIter {
            pos: Some(self),
            max_size: size,
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
    pub fn needed_size(self) -> BoardSize {
        BoardSize(self.column.max(self.row) + 1)
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

pub fn count_possible_placements(max_size: BoardSize, func: &mut dyn FnMut(BoardSize, u64)) {
    for size in (1..=max_size.0).map(BoardSize) {
        // TODO: Improve this
        func(size, naive_count_possible_placements(size));
    }
}

/// This algorithm works reliably, but duplicates work when several sizes are asked for in sequence.
pub fn naive_count_possible_placements(size: BoardSize) -> u64 {
    let spaces = size.available_spaces();
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
    use super::*;

    const EXAMPLE_EXPECTED: &[u64] = &[0, 6, 28, 96, 252, 550, 1056, 1848];
    #[test]
    fn example_naive() {
        for (index, &expected) in EXAMPLE_EXPECTED.iter().enumerate() {
            assert_eq!(
                naive_count_possible_placements(BoardSize(u32::try_from(index).unwrap() + 1)),
                expected
            )
        }
    }

    #[test]
    fn example() {
        let mut res = Vec::new();
        count_possible_placements(BoardSize(8), &mut |size, count| {
            assert_eq!(size.index() as usize, res.len());
            res.push(count);
        });
        assert_eq!(res, EXAMPLE_EXPECTED);
    }

    #[test]
    fn iter_spiral() {
        const MATRIX2: [[char; 2]; 2] = [
            ['A', 'B'], // row1
            ['C', 'D'],
        ];
        assert_eq!(
            BoardSize(2)
                .all_positions()
                .map(|x| MATRIX2[x.row as usize][x.column as usize])
                .collect::<Vec<_>>(),
            vec!['A', 'B', 'D', 'C']
        );
        const MATRIX3: [[char; 3]; 3] = [['A', 'B', 'C'], ['D', 'E', 'F'], ['G', 'H', 'I']];
        assert_eq!(
            BoardSize(3)
                .all_positions()
                .map(|x| MATRIX3[x.row as usize][x.column as usize])
                .collect::<Vec<_>>(),
            vec!['A', 'B', 'E', 'D', 'C', 'F', 'I', 'H', 'G']
        );
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
