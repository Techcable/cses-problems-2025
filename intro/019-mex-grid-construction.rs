use std::fmt::Display;

use self::matrix::Matrix;
use crate::bitset::SmallBitset;
use crate::matrix::MatrixSize;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let input = input.trim();
    let target_size: usize = input.parse()?;
    let res = problem(target_size);
    let mut buffer = String::new();
    for row in 0..target_size {
        buffer.clear();
        join_into(
            (0..target_size).map(|col| res[(row, col)]),
            " ",
            &mut buffer,
        );
        println!("{buffer}");
    }
    Ok(())
}
fn join_into<T: Display>(x: impl IntoIterator<Item = T>, sep: &str, buffer: &mut String) {
    for (index, item) in x.into_iter().enumerate() {
        if index > 0 {
            buffer.push_str(sep);
        }
        use std::fmt::Write;
        write!(buffer, "{item}").unwrap();
    }
}

pub const MAX_SIZE: usize = 100;
#[allow(clippy::cast_possible_truncation)] // not possible
const _: () = {
    assert!((MAX_SIZE as u32).checked_pow(2).is_some());
};
pub fn problem(final_size: usize) -> Matrix<usize> {
    let final_matrix_size = MatrixSize::square(final_size);
    let mut res = Matrix::repeated(final_matrix_size, usize::MAX);
    let mut used_by_col = vec![SmallBitset::new(); final_size];
    let mut used_by_row = vec![SmallBitset::new(); final_size];
    let mut take_next_available = |pos: (usize, usize)| {
        let (row, col) = pos;
        let used = &used_by_col[col] | &used_by_row[row];
        let val = used.lowest_unset().expect("overflow 100^2 not possible");
        eprintln!("taking {val} for ({row}, {col})");
        res[(row, col)] = val;
        assert!(used_by_col[col].insert(val));
        assert!(used_by_row[row].insert(val));
    };
    // the radius controls which row/column we are dealing with
    // radius=0 means we are dealing with
    // x x x x
    // x * * *
    // x * * *
    // x * * *
    // radius=1 means we are dealing with
    // * * * *
    // * x x x
    // * x * *
    // * x * *
    for radius in 0..final_size {
        // determines the step within the radius
        // both vertical and horizontal positions are set in this iteration
        for step in radius..final_size {
            let x = (radius, step);
            let y = (step, radius);
            take_next_available(x);
            if y != x {
                take_next_available(y);
            }
        }
    }
    res
}

mod bitset {
    use std::ops::BitOr;

    #[derive(Clone, Debug)]
    pub struct SmallBitset(u128);
    impl SmallBitset {
        const CAP: usize = 128;
        pub fn from_bits(x: u128) -> Self {
            SmallBitset(x)
        }
        pub fn new() -> Self {
            SmallBitset(0)
        }
        #[inline]
        pub fn lowest_unset(&self) -> Option<usize> {
            if self.0 < u128::MAX {
                // 1111 => 4
                // 1011 => 1
                Some(self.0.trailing_ones() as usize)
            } else {
                None
            }
        }
        #[track_caller]
        #[must_use]
        pub fn contains(&self, x: usize) -> bool {
            (self.0 & self.mask(x)) != 0
        }
        #[track_caller]
        pub fn insert(&mut self, x: usize) -> bool {
            let was_present = self.contains(x);
            self.0 |= self.mask(x);
            !was_present
        }
        #[track_caller]
        fn mask(&self, x: usize) -> u128 {
            1u128 << self.check_bounds(x)
        }
        #[track_caller]
        #[inline]
        #[allow(clippy::cast_possible_truncation)] // we check for this
        fn check_bounds(&self, x: usize) -> u32 {
            let _ = self;
            assert!(x < Self::CAP, "index out of bounds: {x}");
            x as u32
        }
    }
    impl BitOr for SmallBitset {
        type Output = SmallBitset;

        fn bitor(self, rhs: Self) -> Self::Output {
            SmallBitset(self.0 | rhs.0)
        }
    }
    impl BitOr for &SmallBitset {
        type Output = SmallBitset;
        fn bitor(self, rhs: Self) -> Self::Output {
            self.clone() | rhs.clone()
        }
    }
}

mod matrix {
    use std::cell::RefCell;
    use std::fmt::{self, Debug, Display, Write};
    use std::ops::{Index, IndexMut};

    #[derive(Eq, PartialEq, Clone)]
    pub struct Matrix<T> {
        /// Items stored in row-major order.
        items: Box<[T]>,
        size: MatrixSize,
    }
    impl<const ROWS: usize, const COLS: usize, T> From<[[T; COLS]; ROWS]> for Matrix<T> {
        fn from(orig: [[T; COLS]; ROWS]) -> Self {
            Self::from_nested_iters(
                MatrixSize {
                    rows: ROWS,
                    cols: COLS,
                },
                orig,
            )
        }
    }
    impl<T> Matrix<T> {
        pub fn from_nested_iters<R, C>(size: MatrixSize, rows: R) -> Self
        where
            R: IntoIterator<Item = C>,
            C: IntoIterator<Item = T>,
        {
            let num_entries = size.total_entries();
            let mut res = Vec::with_capacity(num_entries);
            let mut rows = rows.into_iter();
            for row in 0..size.rows {
                let mut cols = match rows.next() {
                    Some(cols) => cols.into_iter(),
                    None => panic!("Expected {} rows but got only {row}", size.rows),
                };
                for col in 0..size.cols {
                    let Some(item) = cols.next() else {
                        panic!(
                            "Expected {} columns for row {row} but got only {col}",
                            size.cols
                        );
                    };
                    assert_eq!(res.len(), size.raw_index(row, col));
                    res.push(item);
                }
                expect_no_more(cols, size.cols, format_args!("columns for row {row}"));
            }
            expect_no_more(rows, size.rows, "rows");
            assert_eq!(res.len(), num_entries);
            Matrix {
                items: res.into_boxed_slice(),
                size,
            }
        }
        pub fn from_defaults(size: MatrixSize) -> Self
        where
            T: Default,
        {
            Self::from_fn(size, |_, _| Default::default())
        }
        pub fn repeated(size: MatrixSize, element: T) -> Self
        where
            T: Clone,
        {
            Self::from_fn(size, |_, _| element.clone())
        }
        pub fn from_fn(size: MatrixSize, f: impl FnMut(usize, usize) -> T) -> Self {
            let f = RefCell::new(f);
            Self::from_nested_iters(
                size,
                (0..size.rows).map(|row| {
                    let f = &f;
                    (0..size.cols).map(move |col| f.borrow_mut()(row, col))
                }),
            )
        }

        pub fn set_row(&mut self, row: usize, entries: impl IntoIterator<Item = T>) {
            self.size.check_row(row);
            self.set_bulk_partially(
                (0..self.size.cols).map(|col| (row, col)),
                entries.into_iter(),
            );
        }
        pub fn set_col(&mut self, col: usize, entries: impl IntoIterator<Item = T>) {
            self.size.check_col(col);
            self.set_bulk_partially(
                (0..self.size.cols).map(|row| (row, col)),
                entries.into_iter(),
            );
        }
        #[track_caller]
        fn set_bulk_partially(
            &mut self,
            indexes: impl ExactSizeIterator<Item = (usize, usize)>,
            mut entries: impl Iterator<Item = T>,
        ) {
            let count = indexes.len();
            for (row, col) in indexes {
                let Some(item) = entries.next() else {
                    return;
                };
                self[(row, col)] = item;
            }
            expect_no_more(entries, count, "items");
        }

        #[inline]
        pub fn size(&self) -> MatrixSize {
            self.size
        }
    }
    #[track_caller]
    fn expect_no_more<T>(mut iter: impl Iterator<Item = T>, count: usize, desc: impl Display) {
        if iter.next().is_some() {
            let actual_count = count.saturating_add(1usize).saturating_add(iter.count());
            panic!("Expected at most {count} {desc}, but got {actual_count}")
        }
    }
    impl<T> Index<(usize, usize)> for Matrix<T> {
        type Output = T;

        #[inline]
        #[track_caller]
        fn index(&self, (row, col): (usize, usize)) -> &Self::Output {
            &self.items[self.size.raw_index(row, col)]
        }
    }
    impl<T> IndexMut<(usize, usize)> for Matrix<T> {
        #[inline]
        #[track_caller]
        fn index_mut(&mut self, (row, col): (usize, usize)) -> &mut Self::Output {
            &mut self.items[self.size.raw_index(row, col)]
        }
    }
    /// Displays a matrix with newlines separating rows and spaces separating columns
    impl<T: Display> Display for Matrix<T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            for row in 0..self.size.rows {
                if row > 0 {
                    f.write_char('\n')?;
                }
                for col in 0..self.size.cols {
                    if col > 0 {
                        f.write_char(' ')?;
                    }
                    write!(f, "{}", self[(row, col)])?;
                }
            }
            Ok(())
        }
    }
    impl<T: Debug> Debug for Matrix<T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            struct RowDebug<'a, T: 'a> {
                row: usize,
                matrix: &'a Matrix<T>,
            }
            impl<T: Debug> Debug for RowDebug<'_, T> {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    f.debug_list()
                        .entries(
                            (0..self.matrix.size.cols).map(|col| &self.matrix[(self.row, col)]),
                        )
                        .finish()?;
                    if self.row + 1 < self.matrix.size.rows && !f.alternate() {
                        f.write_char('\n')?;
                    }
                    Ok(())
                }
            }
            f.debug_list()
                .entries((0..self.size.rows).map(|row| RowDebug { row, matrix: self }))
                .finish()
        }
    }
    #[derive(Copy, Clone, Eq, PartialEq)]
    pub struct MatrixSize {
        pub rows: usize,
        pub cols: usize,
    }
    impl MatrixSize {
        #[inline]
        pub fn square(size: usize) -> Self {
            MatrixSize {
                rows: size,
                cols: size,
            }
        }
        #[track_caller]
        #[inline]
        pub fn total_entries(self) -> usize {
            #[cold]
            fn overflow(size: MatrixSize) -> ! {
                panic!("total entries overflowed usize for {size}")
            }
            self.rows
                .checked_mul(self.cols)
                .unwrap_or_else(|| overflow(self))
        }

        #[inline]
        pub fn all_indices(self) -> impl Iterator<Item = (usize, usize)> + 'static {
            (0..self.rows).flat_map(move |row| (0..self.cols).map(move |col| (row, col)))
        }

        /// Determine the raw array index from the row and column,
        /// assuming row-major order.
        #[inline]
        #[track_caller]
        pub fn raw_index(&self, row: usize, col: usize) -> usize {
            self.check_row(row);
            self.check_col(col);
            // should not overflow provided that self.total_entries() doesn't overflow
            (row * self.cols) + col
        }

        #[inline]
        #[track_caller]
        fn check_row(&self, row: usize) {
            assert!(row < self.rows, "Invalid row {row:?} for {self}");
        }
        #[inline]
        #[track_caller]
        fn check_col(&self, col: usize) {
            assert!(col < self.cols, "Invalid column {col:?} for {self}");
        }
    }
    impl Debug for MatrixSize {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "MatrixSize({self})")
        }
    }
    impl Display for MatrixSize {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}x{}", self.rows, self.cols)
        }
    }
}

#[cfg(test)]
mod tests {
    use indoc::indoc;
    use proptest::proptest;
    use similar_asserts::assert_eq;

    use crate::bitset::SmallBitset;
    use crate::matrix::{Matrix, MatrixSize};

    proptest! {
        #[test]
        fn bitset_lowest_set(bits in proptest::bits::u128::ANY) {
            let set = SmallBitset::from_bits(bits);
            let first_actually_missing = (0usize..128).find(|&idx| !set.contains(idx));
            assert_eq!(
                first_actually_missing,
                set.lowest_unset(),
                "{set:?}"
            );
        }
    }

    #[test]
    fn example() {
        check_equal(
            super::problem(5),
            Matrix::from([
                [0, 1, 2, 3, 4],
                [1, 0, 3, 2, 5],
                [2, 3, 0, 1, 6],
                [3, 2, 1, 0, 7],
                [4, 5, 6, 7, 0],
            ]),
        );
    }

    #[test]
    fn test2() {
        let expected = parse_output(
            10,
            indoc!(
                "0 1 2 3 4 5 6 7 8 9
            1 0 3 2 5 4 7 6 9 8
            2 3 0 1 6 7 4 5 10 11
            3 2 1 0 7 6 5 4 11 10
            4 5 6 7 0 1 2 3 12 13
            5 4 7 6 1 0 3 2 13 12
            6 7 4 5 2 3 0 1 14 15
            7 6 5 4 3 2 1 0 15 14
            8 9 10 11 12 13 14 15 0 1
            9 8 11 10 13 12 15 14 1 0"
            ),
        );
        check_equal(super::problem(10), expected);
    }
    #[track_caller]
    #[allow(clippy::needless_pass_by_value)] // can still pass reference if desired
    fn check_equal<T: ToString + Eq>(actual: T, expected: T) {
        if actual != expected {
            assert_eq!(
                actual: actual.to_string(),
                expected: expected.to_string()
            );
        }
    }
    fn parse_output(n: usize, s: &str) -> Matrix<usize> {
        let lines = s.trim().lines().collect::<Vec<_>>();
        assert_eq!(lines.len(), n);
        Matrix::from_nested_iters(
            MatrixSize::square(n),
            lines
                .iter()
                .map(|line| line.split_whitespace().map(|s| s.parse::<usize>().unwrap())),
        )
    }
}
