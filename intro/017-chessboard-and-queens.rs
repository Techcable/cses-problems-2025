use chess_matrix::{ChessBitMatrix, ChessMatrix, MatrixIndex};

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let reserved = input.parse::<ChessBitMatrix>()?;
    println!("{}", problem(reserved));
    Ok(())
}

pub fn problem(reserved: ChessBitMatrix) -> u64 {
    count_sols(State::new(8).with_reserved(reserved))
}
struct State {
    queen_attack_table: &'static QueenAttackTable,
    forbidden_positions: ChessBitMatrix,
    level: usize,
    queen_placements: Vec<MatrixIndex>,
    current_num_queens: u32,
    target_num_queens: u32,
}
impl State {
    fn new(target_num_queens: u32) -> Self {
        use std::sync::OnceLock;
        static QUEEN_ATTACK_TABLE: OnceLock<QueenAttackTable> = OnceLock::new();
        State {
            queen_attack_table: QUEEN_ATTACK_TABLE.get_or_init(queen_attack_table),
            forbidden_positions: ChessBitMatrix::new(),
            queen_placements: Vec::with_capacity(target_num_queens as usize),
            level: 0,
            current_num_queens: 0,
            target_num_queens,
        }
    }
    fn with_reserved(&mut self, reserved: ChessBitMatrix) -> &mut Self {
        assert_eq!(
            self.current_num_queens, 0,
            "cannot reserve after started working"
        );
        self.forbidden_positions = reserved;
        self
    }
    fn with_additional_queen<R>(
        &mut self,
        queen_pos: MatrixIndex,
        func: impl FnOnce(&mut Self) -> R,
    ) -> R {
        assert!(self.current_num_queens < self.target_num_queens);
        self.current_num_queens += 1;
        let new_num_queens = self.current_num_queens;
        self.queen_placements.push(queen_pos);
        let res = func(self);
        assert_eq!(self.current_num_queens, new_num_queens);
        self.current_num_queens -= 1;
        assert_eq!(self.queen_placements.pop(), Some(queen_pos));
        res
    }
}
const MAY_DEBUG: bool = true;
fn should_debug() -> bool {
    use std::sync::OnceLock;
    static SHOULD_DEBUG: OnceLock<bool> = OnceLock::new();
    MAY_DEBUG
        && *SHOULD_DEBUG
            .get_or_init(|| std::env::var_os("NICKNINJA_DEBUG").is_some_and(|x| x == "1"))
}
fn count_sols(state: &mut State) -> u64 {
    if should_debug() {
        let indent = "  ".repeat(state.level);
        for line in format!(
            "forbidden with card {card}, queens {num_queens}\n{table}",
            num_queens = state.current_num_queens,
            table = state.forbidden_positions,
            card = state.forbidden_positions.cardinality()
        )
        .lines()
        {
            eprintln!("{indent}{line}");
        }
    }
    assert!(state.current_num_queens <= state.target_num_queens);
    assert_eq!(
        state.queen_placements.len(),
        state.current_num_queens as usize
    );
    if state.current_num_queens == state.target_num_queens {
        if should_debug() {
            let indent = "  ".repeat(state.level);
            eprintln!("{indent}placement {:?}", state.queen_placements);
        }
        return 1;
    } else if state.forbidden_positions.is_full() {
        return 0;
    }
    state
        .forbidden_positions
        .zeros()
        .map(|free_pos| {
            if should_debug() {
                let indent = "  ".repeat(state.level);
                eprintln!("{indent}free pos {free_pos:?}");
            }
            debug_assert!(!state.forbidden_positions.get(free_pos.row, free_pos.col));
            let attacks = state.queen_attack_table[free_pos];
            // should attack itself
            debug_assert!(attacks.get(free_pos.row, free_pos.col));
            let new_forbidden_positions = state.forbidden_positions | attacks;
            debug_assert!(
                new_forbidden_positions.cardinality() > state.forbidden_positions.cardinality()
            );
            state.with_additional_queen(free_pos, count_sols)
        })
        .sum::<u64>()
}

type QueenAttackTable = ChessMatrix<ChessBitMatrix>;
/// Precompute the positions where a queen would attack.
fn queen_attack_table() -> QueenAttackTable {
    ChessMatrix::from_fn(compute_queen_attacks)
}
fn compute_queen_attacks(pos: MatrixIndex) -> ChessBitMatrix {
    let mut matrix = ChessBitMatrix::new();
    #[inline]
    fn checked_delta_index(x: usize, delta: isize) -> Option<usize> {
        x.checked_add_signed(delta).filter(|&res| res < 8)
    }
    #[inline]
    fn checked_delta_pos(
        x: MatrixIndex,
        delta_row: isize,
        delta_col: isize,
    ) -> Option<MatrixIndex> {
        let row = checked_delta_index(x.row, delta_row)?;
        let col = checked_delta_index(x.col, delta_col)?;
        Some(MatrixIndex { row, col })
    }
    const DELTAS: [(isize, isize); 4] = [(1, 1), (-1, -1), (-1, 1), (1, -1)];
    for i in 0..8usize {
        matrix.set(pos.row, i, true);
        matrix.set(i, pos.col, true);
        for (mut delta_row, mut delta_col) in DELTAS {
            #[allow(clippy::cast_possible_wrap)] // will not overflow for i<8
            {
                delta_row *= i as isize;
                delta_col *= i as isize;
            }
            if let Some(diagonal) = checked_delta_pos(pos, delta_row, delta_col) {
                matrix.set(diagonal.row, diagonal.col, true);
            }
        }
    }
    matrix
}

#[allow(clippy::trivially_copy_pass_by_ref)]
pub mod chess_matrix {
    use std::fmt::{self, Debug, Display, Write};
    use std::option::Option;
    use std::str::FromStr;

    #[derive(Clone)]
    pub struct ChessMatrix<V> {
        matrix: [V; 64],
    }
    impl<V> ChessMatrix<V> {
        pub const ROWS: usize = 8;
        pub const COLS: usize = 8;
        pub const SIZE: usize = Self::ROWS * Self::COLS;
        pub fn from_fn(mut fun: impl FnMut(MatrixIndex) -> V) -> Self {
            ChessMatrix {
                matrix: std::array::from_fn(|index| {
                    fun(MatrixIndex {
                        row: index / Self::COLS,
                        col: index % Self::COLS,
                    })
                }),
            }
        }
        #[inline]
        #[track_caller]
        fn full_index(index: MatrixIndex) -> usize {
            let MatrixIndex { row, col } = index;
            if row >= Self::ROWS || col >= Self::COLS {
                ChessBitMatrix::out_of_bounds(index)
            }
            row * Self::COLS + col
        }
    }
    impl<V> std::ops::Index<MatrixIndex> for ChessMatrix<V> {
        type Output = V;
        fn index(&self, index: MatrixIndex) -> &Self::Output {
            let full_index = Self::full_index(index);
            &self.matrix[full_index]
        }
    }
    impl<V> std::ops::Index<(u32, u32)> for ChessMatrix<V> {
        type Output = V;
        #[inline]
        fn index(&self, index: (u32, u32)) -> &V {
            &self[MatrixIndex::from(index)]
        }
    }
    impl<V> std::ops::IndexMut<MatrixIndex> for ChessMatrix<V> {
        #[inline]
        fn index_mut(&mut self, index: MatrixIndex) -> &mut V {
            let index = Self::full_index(index);
            &mut self.matrix[index]
        }
    }

    #[derive(Copy, Clone, Default)]
    pub struct ChessBitMatrix {
        /// A 2d bit-matrix using row-major order
        bits: u64,
    }
    impl ChessBitMatrix {
        pub const ROWS: usize = 8;
        pub const COLS: usize = 8;
        pub const SIZE: usize = Self::ROWS * Self::COLS;

        #[inline]
        pub const fn new() -> Self {
            assert!(Self::SIZE == u64::BITS as usize);
            ChessBitMatrix { bits: 0 }
        }
        #[inline]
        pub fn cardinality(&self) -> usize {
            self.bits.count_ones() as usize
        }
        #[inline]
        pub fn is_full(&self) -> bool {
            self.bits == u64::MAX
        }
        #[inline]
        pub fn ones(&self) -> PosIter {
            PosIter {
                remaining_word: self.bits,
            }
        }
        #[inline]
        pub fn zeros(&self) -> PosIter {
            PosIter {
                remaining_word: !self.bits,
            }
        }
        #[inline] // want const-folding and DCE
        #[track_caller]
        pub fn set(&mut self, row: usize, col: usize, new_value: bool) -> bool {
            let index = Self::bit_index(MatrixIndex { row, col });
            let old_word = self.bits;
            if new_value {
                self.bits |= index.mask();
            } else {
                self.bits &= !index.mask();
            }
            old_word & index.mask() != 0
        }
        #[track_caller]
        #[inline]
        fn bit_index(matrix_index: MatrixIndex) -> BitIndex {
            let MatrixIndex { row, col } = matrix_index;
            if row >= Self::ROWS || col >= Self::COLS {
                Self::out_of_bounds(matrix_index)
            }
            #[allow(clippy::cast_possible_truncation)] // effectively checked above
            BitIndex {
                bit_index: (row as u32) * (Self::COLS as u32) + (col as u32),
            }
        }
        #[inline]
        fn matrix_index(bit_index: BitIndex) -> MatrixIndex {
            let BitIndex {
                bit_index: full_index,
            } = bit_index;
            let full_index = full_index as usize;
            if full_index >= Self::SIZE {
                Self::out_of_bounds(full_index)
            }
            MatrixIndex {
                row: full_index / Self::COLS,
                col: full_index % Self::COLS,
            }
        }
        #[track_caller]
        #[cold]
        fn out_of_bounds(index: impl Debug) -> ! {
            panic!(
                "index {index:?} out of bounds for {}x{} matrix",
                Self::ROWS,
                Self::COLS
            );
        }
        #[inline]
        #[track_caller]
        pub fn get(&self, row: usize, col: usize) -> bool {
            let index = Self::bit_index(MatrixIndex { row, col });
            self.bits & index.mask() != 0
        }
    }
    #[derive(Clone)]
    pub struct PosIter {
        remaining_word: u64,
    }
    impl Iterator for PosIter {
        type Item = MatrixIndex;
        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            let count = self.remaining_word.count_ones() as usize;
            (count, Some(count))
        }
        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            if self.remaining_word != 0 {
                let one_index = self.remaining_word.trailing_zeros();
                self.remaining_word &= !(1 << one_index);
                Some(ChessBitMatrix::matrix_index(BitIndex {
                    bit_index: one_index,
                }))
            } else {
                None
            }
        }
    }
    impl std::iter::ExactSizeIterator for PosIter {}
    impl std::iter::FusedIterator for PosIter {}
    impl FromStr for ChessBitMatrix {
        type Err = BoardParseError;
        fn from_str(s: &str) -> Result<Self, Self::Err> {
            let mut res = ChessBitMatrix::new();
            let mut seen_lines = 0;
            for (row, line) in s.lines().enumerate() {
                let lineno = row + 1;
                if row > Self::ROWS {
                    return Err(BoardParseError("too many lines".into()));
                }
                seen_lines += 1;
                if line.len() != 8 {
                    return Err(BoardParseError(format!(
                        "line #{lineno} has wrong number of columns"
                    )));
                }
                for (col, c) in line.chars().enumerate() {
                    match c {
                        '.' => {}
                        '*' => {
                            assert!(!res.set(row, col, true));
                        }
                        _ => return Err(BoardParseError(format!("invalid char {c:?}"))),
                    }
                }
            }
            if seen_lines < 8 {
                return Err(BoardParseError("not enough lines".into()));
            }
            Ok(res)
        }
    }
    #[derive(Debug, Clone)]
    pub struct BoardParseError(String);
    impl Display for BoardParseError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "failed to parse chess board: {}", self.0)
        }
    }
    impl std::error::Error for BoardParseError {}
    impl Display for ChessBitMatrix {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            for row in 0..Self::COLS {
                if row > 0 {
                    f.write_char('\n')?;
                }
                for col in 0..Self::ROWS {
                    if self.get(row, col) {
                        f.write_char('*')?;
                    } else {
                        f.write_char('.')?;
                    }
                }
            }
            Ok(())
        }
    }
    impl std::ops::BitOr for ChessBitMatrix {
        type Output = Self;
        #[inline]
        fn bitor(self, other: Self) -> Self::Output {
            ChessBitMatrix {
                bits: self.bits | other.bits,
            }
        }
    }
    impl std::ops::BitAnd for ChessBitMatrix {
        type Output = Self;
        #[inline]
        fn bitand(self, other: Self) -> Self {
            ChessBitMatrix {
                bits: self.bits & other.bits,
            }
        }
    }
    #[derive(Copy, Clone, Debug)]
    struct BitIndex {
        bit_index: u32,
    }
    impl BitIndex {
        #[inline]
        fn mask(self) -> u64 {
            1u64 << self.bit_index
        }
    }
    #[derive(Copy, Clone, Eq, PartialEq)]
    pub struct MatrixIndex {
        pub row: usize,
        pub col: usize,
    }
    impl MatrixIndex {
        #[inline]
        pub const fn new(row: usize, col: usize) -> Self {
            Self { row, col }
        }
    }
    impl Debug for MatrixIndex {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "({}, {})", self.row, self.col)
        }
    }
    impl From<(u32, u32)> for MatrixIndex {
        #[inline]
        fn from(value: (u32, u32)) -> Self {
            MatrixIndex {
                row: value.0 as usize,
                col: value.1 as usize,
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::{count_sols, problem, State};
    use indoc::indoc;

    const EXAMPLE_INPUT_STR: &str = indoc!(
        "........
        ........
        ..*.....
        ........
        ........
        .....**.
        ...*....
        ........"
    );

    #[test]
    fn example() {
        assert_eq!(problem(EXAMPLE_INPUT_STR.parse().unwrap()), 65);
    }

    const TWO_QUEENS1: &str = indoc!(
        "********
        ********
        ********
        ********
        ********
        ********
        ...*....
        ........"
    );
    #[test]
    fn two_queens1() {
        assert_eq!(
            count_sols(State::new(2).with_reserved(TWO_QUEENS1.parse().unwrap())),
            56
        );
    }
}
