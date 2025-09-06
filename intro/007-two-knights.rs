use std::cmp::Ordering;
use std::ops::{Add, RangeInclusive, Sub};
use std::sync::OnceLock;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let input = input.trim().parse::<u32>()?;
    count_possible_placements(BoardSize::new(input), &mut |_size, total| {
        println!("{total}");
    });
    // just used to ensure nothing overflows a u32
    let _ = MAX_BOARD_SPACES;
    Ok(())
}

const MAX_INPUT: u32 = 10_000;
const MAX_BOARD_SPACES: u32 = MAX_INPUT * MAX_INPUT;

#[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct BoardSize {
    index: u32,
}
impl BoardSize {
    pub const MIN: BoardSize = BoardSize { index: 0 };
    #[inline]
    #[track_caller]
    pub const fn new(value: u32) -> BoardSize {
        assert!(value >= 1, "invalid size");
        BoardSize { index: value - 1 }
    }
    #[inline]
    pub const fn from_index(index: u32) -> BoardSize {
        BoardSize { index }
    }
    pub fn all_positions(self) -> impl Iterator<Item = Position> + 'static {
        Position { row: 0, column: 0 }.remaining_positions(self)
    }
    #[inline]
    pub fn available_spaces(&self) -> u32 {
        self.value() * self.value()
    }
    #[inline]
    pub fn value(&self) -> u32 {
        self.index + 1
    }
    #[inline]
    pub fn max_spiral_index(&self) -> u32 {
        self.index * 2
    }
    #[inline]
    pub fn fixed_spiral(self) -> FixedSizeSpiral {
        FixedSizeSpiral {
            counter: 0..=self.max_spiral_index(),
            size: self,
        }
    }
    /// Return the position corresponding to the specified spiral index.
    ///
    /// Used to implement [`FixedSizeSpiral`] and [`BoardSpiral`].
    ///
    /// Starts from the top right, goes down then turns left after hitting the bottom.
    #[inline]
    pub fn pos_at_spiral_index(self, index: u32) -> Position {
        let max_spiral_index = self.max_spiral_index();
        assert!(index <= max_spiral_index);
        Position {
            // column should decrease once `index > self.index`
            column: (max_spiral_index - index).min(self.index),
            // row should increase until we hit the maximum
            row: index.min(self.index),
        }
    }
}
impl Add<u32> for BoardSize {
    type Output = BoardSize;
    #[track_caller]
    fn add(self, rhs: u32) -> Self::Output {
        BoardSize::from_index(self.index.checked_add(rhs).expect("addition overflow"))
    }
}

impl Sub<u32> for BoardSize {
    type Output = BoardSize;
    #[track_caller]
    fn sub(self, rhs: u32) -> Self::Output {
        BoardSize::from_index(self.index.checked_sub(rhs).expect("subtraction underflow"))
    }
}

/// An iterator that spirals over the entries of a fixed [`BoardSize`].
///
/// Used to implement [`Position::remaining_positions`] and [`BoardSpiral`].
#[derive(Clone)]
pub struct FixedSizeSpiral {
    counter: RangeInclusive<u32>,
    size: BoardSize,
}
impl Iterator for FixedSizeSpiral {
    type Item = Position;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.counter
            .next()
            .map(|index| self.size.pos_at_spiral_index(index))
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.counter.size_hint()
    }
}
impl DoubleEndedIterator for FixedSizeSpiral {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.counter
            .next_back()
            .map(|index| self.size.pos_at_spiral_index(index))
    }
}
impl ExactSizeIterator for FixedSizeSpiral {}

/// Spirals across the chess board:
///
/// Assume the following board with the top left at position (0, 0)
/// ```
/// A B
/// D C
/// ```
/// The iterator will give `[A, B, C, D]`
#[derive(Clone)]
pub struct BoardSpiral {
    current_spiral: FixedSizeSpiral,
    max_size: BoardSize,
}
impl Iterator for BoardSpiral {
    type Item = Position;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self.current_spiral.next() {
            Some(res) => Some(res),
            None => {
                if self.current_spiral.size < self.max_size {
                    self.current_spiral = (self.current_spiral.size + 1).fixed_spiral();
                    Some(self.current_spiral.next().unwrap())
                } else {
                    None
                }
            }
        }
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
    fn remaining_positions(self, max_size: BoardSize) -> impl Iterator<Item = Position> + 'static {
        let current_size = self.needed_size();
        BoardSpiral {
            current_spiral: FixedSizeSpiral {
                size: current_size,
                counter: self.determine_spiral_index()..=current_size.max_spiral_index(),
            },
            max_size,
        }
    }
    #[inline]
    pub fn checked_offset(self, offset: Offset, size: BoardSize) -> Option<Position> {
        Some(Position {
            row: self
                .row
                .checked_add_signed(offset.row)
                .filter(|&x| x <= size.index)?,
            column: self
                .column
                .checked_add_signed(offset.column)
                .filter(|&x| x <= size.index)?,
        })
    }
    #[inline]
    pub fn needed_size(self) -> BoardSize {
        BoardSize::from_index(self.column.max(self.row))
    }
    /// Determine the spiral index for this position within
    /// the spiral returned by calling [`BoardSize::fixed_spiral`] on [`Self::needed_size`].
    ///
    /// This is the opposite of [`BoardSize::pos_at_spiral_index`].
    #[inline]
    pub fn determine_spiral_index(self) -> u32 {
        if self.row <= self.column {
            // going down
            self.row
        } else {
            // going left (column decreasing, row=needed_size)
            let size = self.needed_size();
            debug_assert_eq!(size.index, self.row);
            size.index + (size.index - self.column)
        }
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
    let knight_movements = knight_movements();
    if max_size.value() < 1 {
        return;
    }
    let mut total_possibilities = 0u64;
    func(BoardSize::MIN, total_possibilities);
    for current_size in (2..=max_size.value()).map(BoardSize::new) {
        let prev_size = current_size - 1;
        // only iterate over the outer layer of the spiral,
        // since that is the only one with new positions
        for (knight_pos, knight_pos_index) in current_size
            .fixed_spiral()
            .zip(prev_size.available_spaces()..)
        {
            // valid combos with this position are every previous position
            let mut valid_combos = knight_pos_index;
            for &movement in knight_movements {
                // check if the movement would escape the board
                if let Some(pos) = knight_pos.checked_offset(movement, current_size) {
                    if pos > knight_pos {
                        /* will deal with this later */
                    } else {
                        valid_combos -= 1;
                    }
                }
            }
            total_possibilities += valid_combos as u64;
        }
        func(current_size, total_possibilities);
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
                naive_count_possible_placements(BoardSize::from_index(
                    u32::try_from(index).unwrap()
                )),
                expected
            );
        }
    }

    #[test]
    fn example() {
        let mut res = Vec::new();
        count_possible_placements(BoardSize::new(8), &mut |size, count| {
            assert_eq!(size.index as usize, res.len());
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
            BoardSize::new(2)
                .all_positions()
                .map(|x| MATRIX2[x.row as usize][x.column as usize])
                .collect::<Vec<_>>(),
            vec!['A', 'B', 'D', 'C']
        );
        const MATRIX3: [[char; 3]; 3] = [['A', 'B', 'C'], ['D', 'E', 'F'], ['G', 'H', 'I']];
        assert_eq!(
            BoardSize::new(3)
                .all_positions()
                .map(|x| MATRIX3[x.row as usize][x.column as usize])
                .collect::<Vec<_>>(),
            vec!['A', 'B', 'E', 'D', 'C', 'F', 'I', 'H', 'G']
        );
    }

    #[test]
    fn iter_order() {
        let size = BoardSize::new(5);
        let mut prev_seen = Vec::new();
        for x in size.all_positions() {
            for &y in &prev_seen {
                assert!(y < x);
            }
            for y in x.remaining_positions(size) {
                assert!(y >= x, "{y:?} < {x:?}");
            }
            prev_seen.push(x);
        }
    }

    #[test]
    fn test_fixed_spiral_endpoints() {
        for size in (BoardSize::MIN.value()..=10).map(BoardSize::new) {
            let start = Position {
                row: 0,
                column: size.index,
            };
            let end = Position {
                row: size.index,
                column: 0,
            };
            let corner = Position {
                row: size.index,
                column: size.index,
            };
            assert_eq!(start, size.pos_at_spiral_index(0), "{size:?}");
            assert_eq!(
                end,
                size.pos_at_spiral_index(size.max_spiral_index()),
                "{size:?}"
            );
            assert_eq!(corner, size.pos_at_spiral_index(size.index), "{size:?}");
            if size.index > 0 {
                assert_eq!(
                    start
                        .checked_offset(Offset { row: 1, column: 0 }, size)
                        .unwrap(),
                    size.pos_at_spiral_index(1)
                );
                assert_eq!(
                    end.checked_offset(Offset { row: 0, column: 1 }, size)
                        .unwrap(),
                    size.pos_at_spiral_index(size.max_spiral_index() - 1)
                );
            }
        }
    }

    #[test]
    fn test_spiral_index() {
        // NOTE: This test assumes that needed_size() works
        let mut last: Option<Position> = None;
        for x in BoardSize::new(5).all_positions() {
            if let Some(last) = last {
                if x.needed_size() > last.needed_size() {
                    assert_eq!(x, x.needed_size().pos_at_spiral_index(0));
                    assert_eq!(
                        last.needed_size()
                            .pos_at_spiral_index(last.needed_size().max_spiral_index()),
                        last
                    );
                }
            } else {
                assert_eq!(BoardSize::MIN.max_spiral_index(), 0);
                assert_eq!(x, BoardSize::MIN.pos_at_spiral_index(0));
                assert_eq!(x, BoardSize::MIN.pos_at_spiral_index(0));
            }
            let spiral_index = x.determine_spiral_index();
            assert_eq!(x.needed_size().pos_at_spiral_index(spiral_index), x);
            last = Some(x);
        }
    }
}
