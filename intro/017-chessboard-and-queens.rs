pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let mut lines = input.lines();
    let matrix = ChessBitMatrix::new();
    Ok(())
}

type ChessBitMatrix = BitMatrix<8, 8, 1>;

mod bit_matrix {
    use std::fmt::Debug;

    struct BitMatrix<const ROWS: usize, const COLS: usize, const WORDS: usize> {
        /// A 2d bit-matrix using row-major order
        bits: [u64; WORDS],
        len: usize,
    }
    impl<const ROWS: usize, const COLS: usize, const WORDS: usize> BitMatrix<ROWS, COLS, WORDS> {
        #[inline]
        const fn _verify_size() {
            const {
                assert!((ROWS * COLS).div_ceil(u64::BITS as usize) == WORDS);
            }
        }
        #[inline]
        pub const fn new() -> Self {
            Self::_verify_size();
            BitMatrix { bits: [0; WORDS] }
        }
        #[inline] // want const-folding and DCE
        #[track_caller]
        pub fn set(&mut self, row: usize, col: usize, new_value: bool) -> bool {
            let index = self.bit_index(MatrixIndex { row, col });
            let old_word = self.bits[index.word_index];
            if new_value {
                self.bits[index.word_index] |= index.mask();
            } else {
                self.bits[index.word_index] &= !index.mask();
            }
            let was_present = old_word & index.mask() != 0;
            match (new_value, was_present) {
                (true, true) | (false, false) => {}
                (true, false) => self.len += 1,
                (false, true) => self.len -= 1,
            }
            was_present
        }
        #[track_caller]
        #[inline]
        fn bit_index(&self, matrix_index: MatrixIndex) -> BitIndex {
            let MatrixIndex { row, col } = matrix_index;
            if row >= ROWS || col >= COLS {
                Self::out_of_bounds(matrix_index)
            }
            let index = row * COLS + col;
            BitIndex {
                word_index: index / u64::BITS,
                bit_index: (index % u64::BITS) as u32,
            }
        }
        #[inline]
        fn matrix_index(&self, bit_index: BitIndex) -> MatrixIndex {
            let full_index = bit_index.full_index();
            if full_index >= ROWS * COLS {
                Self::out_of_bounds(full_index)
            }
            MatrixIndex {
                row: full_index / COLS,
                col: full_index % COLS,
            }
        }
        #[track_caller]
        #[cold]
        fn out_of_bounds(index: impl Debug) -> ! {
            panic!("index {index:?} out of bounds for {ROWS}x{COLS} matrix");
        }
        pub fn ones(&self) -> Ones {}
        #[inline]
        #[track_caller]
        pub fn get(&self, row: usize, col: usize) -> bool {
            let index = self.bit_index(MatrixIndex { row, col });
            self.bits[index.word_index] & index.mask() != 0
        }
    }
    struct Ones<'a> {
        current_word: Option<(usize, u64)>,
        remaining_words: std::iter::Enumerate<std::slice::Iter<'a, u64>>,
        len: usize,
    }
    impl Iterator for Ones<'_> {
        type Item = MatrixIndex;
        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            (self.len, Some(self.len))
        }
        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            loop {
                match self.current_word {
                    None | Some((_, 0)) => {
                        self.current_word = self.remaining_words.next();
                    }
                    Some((word_index, val)) => {
                        let bit_index = val.leading_ones();
                    }
                }
            }
        }
    }
    impl std::iter::FusedIterator for Ones<'_> {}
    impl ExactSizeIterator for Ones<'_> {}
    #[derive(Copy, Clone, Debug)]
    struct BitIndex {
        word_index: usize,
        bit_index: u32,
    }
    impl BitIndex {
        #[inline]
        fn full_index(&self) -> usize {
            (self.word_index * (u64::BITS as usize)) + (self.bit_index as usize)
        }
        #[inline]
        fn mask(&self) -> u64 {
            1u64 << self.bit_index
        }
    }
    #[derive(Copy, Clone, Eq, PartialEq)]
    pub struct MatrixIndex {
        row: usize,
        col: usize,
    }
    impl Debug for MatrixIndex {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "({}, {})", self.row, self.col)
        }
    }
}
