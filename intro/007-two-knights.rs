use std::cmp::Ordering;
use std::fmt::{Debug, Display};
use std::ops::{Add, RangeInclusive, Sub, RangeBounds, Bound, Range};

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

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
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
impl Debug for BoardSize {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("BoardSize")
            .field(&self.value())
            .finish()
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
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Position {
    row: u32,
    column: u32,
}
impl Position {
    #[inline]
    fn remaining_positions_fixed_size(self) -> FixedSizeSpiral {
        let current_size = self.needed_size();
        FixedSizeSpiral {
            size: current_size,
            counter: self.determine_spiral_index()..=current_size.max_spiral_index(),
        }
    }
    #[inline]
    fn remaining_positions(self, max_size: BoardSize) -> impl Iterator<Item = Position> + 'static {
        BoardSpiral {
            current_spiral: self.remaining_positions_fixed_size(),
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
impl Debug for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Position")
            .field(&self.row)
            .field(&self.column)
            .finish()
    }
}
#[derive(Copy, Clone, Debug)]
pub struct Offset {
    row: i32,
    column: i32,
}

macro_rules! const_for {
    (for $name:ident in [$($item:expr),*] $body:block) => {
        $({
            let $name = $item;
            $body
        })*
    };
}
static KNIGHT_MOVEMENTS: [Offset; 8] = {
    let mut res = [Offset { row: 0, column: 0 }; 8];
    let mut idx = 0;
    const_for!(for row_magnitude in [1, 2] {
        let col_magnitude = 3 - row_magnitude;
        const_for!(for row_dir in [-1, 1] {
            const_for!(for col_dir in [-1, 1] {
                res[idx] = Offset {
                    row: row_magnitude * row_dir,
                    column: col_magnitude * col_dir,
                };
                idx += 1;
            });
        });
    });
    assert!(idx == res.len());
    res
};

const AWAY_FROM_CORNERS_DIST: u32 = 3;
const AWAY_FROM_CORNERS_VALID_MOVEMENTS: u32 = 0;
pub fn count_possible_placements(max_size: BoardSize, func: &mut dyn FnMut(BoardSize, u64)) {
    if max_size.value() < 1 {
        return;
    }
    let mut total_possibilities = 0u64;
    func(BoardSize::MIN, total_possibilities);
    for current_size in (2..=max_size.value()).map(BoardSize::new) {
        let prev_size = current_size - 1;
        // the naive implementation has two nested loops
        // In pseudocode:
        // ```
        // let already_handled = set();
        // for knight1_pos in prev_size.fixed_spiral() {
        //      let mut possible_combos = [possible placements of knight2 not already handled]
        //      for moved_pos in possible_movements(knight_pos) {
        //          if moved_pos not in already_handled {
        //              // a knight can attach from knight1_pos to moved_pos.
        //              // This means moved_pos is not a valid combination
        //              possible_combos -= 1;
        //          }
        //      }
        //      already_handled.add(knight1_pos)
        // }
        // ```
        // NOTE: The inner loop is split into the separate `naive_count_possible_movements` function.
        //
        // When the size is large, most of these inner two iterations
        // are spent far from the edges and corner of the board.
        // In this case, the knight has exactly 4 possible movements that do not fall off the edge of the board.
        // This eliminates the need to check for overflowing positions (done by possible_movements function in pseudocode).
        // When away from the corners, none of these possible movements are onto the outer edge of the spiral,
        // because a knight can't attack the same row/column it is on.
        // This means possible movements is zero unless we are near the corner.
        // This means that in most cases, the number of possible movements is zero
        // and so the subtraction `possible_combos -= 1` is executed zero times.
        // This reasoning is verified by a test, which ensures that away from the edges of the board,
        // there are zero valid movements not already handled.
        //
        // Unfortunately, this is a little more complicated then just turing constant addition into multiplication,
        // because the value of `possible_combos` changes each iteration.
        // Both the naive and optimized implementation take advantage of the fact that we iterate
        // over the spiral in order and that the ordering of a Position respects the order of the spiral.
        // This means we can use a Position comparison to implement `moved_pos not in already_handled`.
        // Even more importantly, it means we can compute the number of `possible_combos` from the index
        // More precisely, the possible combos are exactly the position of
        // This also takes care of some double counting issues.
        // (Note that double counting is why we have the already_handled check in the first place).
        //
        // Anyway, since the index increases by one each time, this is an arithmetic sequence.
        // Luckily, any arithmetic sequence has a simple closed form expression
        // which is handled by the `sum_range` function.
        //
        // Also, we only perform this optimization for large size boards >= 20
        let prev_size_spaces = prev_size.available_spaces();
        eprintln!("prev spaces {prev_size_spaces} for {current_size:?}");

        for spiral_index in 0..=current_size.max_spiral_index() {
            let knight_pos = current_size.pos_at_spiral_index(spiral_index);
            let knight_pos_index = prev_size_spaces + spiral_index;
            // valid combos with this position are every previous position,
            // except those the knight can attack
            let mut valid_combos = knight_pos_index;
            let valid_movements = naive_count_possible_movements(
                knight_pos,
                current_size,
                |other_pos| {
                    // we will handle these positions later
                    // Note that this logic differs from the naive comparison
                    other_pos > knight_pos
                }
            );
            if current_size.index >= 20 && spiral_index >= 5 && (spiral_index.abs_diff(current_size.index)) > 5 && spiral_index <= (current_size.max_spiral_index() - 5) {
                assert_eq!(valid_movements, 4, "{spiral_index} for {current_size:?}");
            }
            valid_combos -= valid_movements;
            eprintln!("opt: valid combos for {knight_pos:?} are {valid_combos}");
            total_possibilities += valid_combos as u64;
        }
        func(current_size, total_possibilities);
    }
}

/// This algorithm works reliably, but duplicates work when several sizes are asked for in sequence.
pub fn naive_count_possible_placements(size: BoardSize) -> u64 {
    let spaces = size.available_spaces();
    let mut total = 0u64;
    // there is symmetry here: Knight A can attack knight B iff B can attack knight B
    // So after placing knight A, then B can be wherever A does not attack
    //
    // In order to avoid double counting, we only count positions >= knight,
    // taking advantage of the total order of Position and the fact the iterator
    // respects that ordering
    for (index, knight) in size.all_positions().enumerate() {
        #[allow(clippy::cast_possible_truncation)] // cannot overflow unless `spaces` does
        let index = index as u32;
        let mut this_board_combos = spaces - 1 - index;
        this_board_combos -= naive_count_possible_movements(knight, size, |other_pos| {
            // The ordering of Position is designed to respect the spiral iteration order.
            // Since we iterate the spiral in order,
            // this means we can use a comparison to check for already visited spaces
            other_pos <= knight
        });
        eprintln!("naive: valid combos for {knight:?} are {this_board_combos} for {size:?}");
        total += this_board_combos as u64;
    }
    total
}

/// Count the possible movements that a knight at position `knight`
/// can make in a board of size `size`.
///
/// This ignores moves that should be ignored according to the specified closure.
///
/// This is shared between the naive implementation and fast implementation,
/// but the faster implementation skips calling this function in many cases.
/// This is also used by a test to ensure the reasoning used by the fast
/// function to skip certain cases remains valid.
fn naive_count_possible_movements(
    knight: Position,
    size: BoardSize,
    should_ignore: impl Fn(Position) -> bool,
) -> u32 {
    let mut possible_movements = 0;
    for movement in KNIGHT_MOVEMENTS {
        if let Some(pos) = knight.checked_offset(movement, size) {
            if !should_ignore(pos) {
                possible_movements += 1;
            }
        }
    }
    possible_movements
}

/// Map the values in the range, as if calling the `range.map()` iterator function.
///
/// However, this returns a range, simply mapping the start and end indexes.
/// This means the transformation has to be implemented sanely for this to work.
pub fn map_range<U: Copy, T>(
    range: RangeInclusive<U>,
    mut func: impl FnMut(U) -> T,
) -> RangeInclusive<T> {
    func(*range.start())..=func(*range.end())
}
/// Sum all the values in the specified range.
///
/// Equivalent to `range.sum()` but takes O(1) time.
pub fn sum_range<R: RangeBounds<u32>>(range: R) -> u64 {
    let Bound::Included(&start) = range.start_bound() else {
        unimplemented!("start bound must be inclusive: {:?}", range.start_bound());
    };
    let len = match range.end_bound() {
        Bound::Included(&end) => {
            assert!(end >= start);
            (end - start) + 1

        }
        Bound::Excluded(&end) => {
            assert!(end >= start);
            end - start
        }
        Bound::Unbounded => panic!("end bound can't be unbounded"),
    } as u64;
    if len == 0 {
        0
    } else {
        (len * start as u64) + ((len * (len - 1)) / 2)
    }
}

/// Split the range `[a, b]` into `[a, mid)` and `[mid, b]`
pub fn split_range<T: PrimInt>(range: RangeInclusive<T>, mid: T) -> (Range<T>, RangeInclusive<T>) {
    assert!(
        *range.start() <= mid && mid <= *range.end(),
        "invalid args: ({range:?}, {mid})"
    );
    (*range.start()..mid, mid..=*range.end())

}
pub trait PrimInt: Ord + Display + Debug + Copy {}
impl PrimInt for u32 {}


#[cfg(test)]
mod test {
    use super::*;

    fn optimized_possible_placements(max_size: BoardSize) -> Vec<u64> {
        // putting this in a single function avoids code duplication
        // and more importantly reduces monomorphization
        let mut res = Vec::new();
        count_possible_placements(max_size, &mut |size, count| {
            assert_eq!(size.index as usize, res.len());
            res.push(count);
        });
        res
    }

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
    fn outside_corners_constant_valid_movements() {
        for size in [20, 30, 40, 42, 62].map(BoardSize::new) {
            let corner_index = size.index;
            let indexes_away_from_edges = Iterator::chain(
                0..=(corner_index - AWAY_FROM_CORNERS_DIST),
                (corner_index + AWAY_FROM_CORNERS_DIST)..=size.max_spiral_index(),
            );
            for spiral_index in indexes_away_from_edges {
                let knight = size.pos_at_spiral_index(spiral_index);
                assert_eq!(
                    naive_count_possible_movements(knight, size, |other_pos| other_pos <= knight),
                    AWAY_FROM_CORNERS_VALID_MOVEMENTS,
                    "index = {spiral_index}, size = {size:?}"
                );
            }
        }
    }

    #[test]
    fn example() {
        assert_eq!(
            optimized_possible_placements(BoardSize::new(8)),
            EXAMPLE_EXPECTED
        );
    }

    #[test]
    fn large_spiral_matches_naive() {
        const START: BoardSize = BoardSize::new(20);
        const END: BoardSize = BoardSize::new(30);
        let naive_results = (START.index..=END.index)
            .map(BoardSize::from_index)
            .map(naive_count_possible_placements)
            .collect::<Vec<_>>();
        let optimized_results = optimized_possible_placements(END)
            .into_iter()
            .enumerate()
            .filter(|(idx, _)| *idx >= START.index as usize)
            .map(|(_, count)| count)
            .collect::<Vec<_>>();
        assert_eq!(naive_results.len(), optimized_results.len());
        assert_eq!(naive_results, optimized_results);
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

    #[test]
    fn verify_sum_range() {
        assert_eq!(sum_range(5..5), 0);
        assert_eq!(sum_range(0..=10), (0..=10).sum());
        assert_eq!(sum_range(5..=20), (5..=20).sum());
        assert_eq!(sum_range(5..20), (5..20).sum());
        assert_eq!(sum_range(482..=1000), (482..=1000).sum());
    }
}
