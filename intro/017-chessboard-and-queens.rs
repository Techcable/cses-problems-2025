use chess_matrix::{ChessBitMatrix, ChessMatrix, MatrixIndex};

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let reserved = input.parse::<ChessBitMatrix>()?;
    let matrix = ChessBitMatrix::new();
    Ok(())
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
    impl<V> std::ops::Index<(u32, u32)> for ChessMatrix<V> {
        type Output = V;
        #[inline]
        fn index(&self, index: (u32, u32)) -> &V {
            let index = Self::full_index(index.into());
            &self.matrix[index]
        }
    }
    impl<V> std::ops::IndexMut<(u32, u32)> for ChessMatrix<V> {
        #[inline]
        fn index_mut(&mut self, index: (u32, u32)) -> &mut V {
            let index = Self::full_index(index.into());
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
        pub fn ones(&self) -> Ones {
            Ones {
                remaining_word: self.bits,
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
    pub struct Ones {
        remaining_word: u64,
    }
    impl Iterator for Ones {
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
                Some(ChessBitMatrix::matrix_index(BitIndex {
                    bit_index: one_index,
                }))
            } else {
                None
            }
        }
    }
    impl std::iter::ExactSizeIterator for Ones {}
    impl std::iter::FusedIterator for Ones {}
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
                        f.write_char('.')?;
                    } else {
                        f.write_char('*')?;
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
