use self::matrix::Matrix;
use crate::matrix::MatrixSize;
use std::fmt::Display;

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
pub fn problem(final_size: usize) -> Matrix<u32> {
    let final_matrix_size = MatrixSize::square(final_size);
    let mut res = Matrix::repeated(final_matrix_size, u32::MAX);
    assert!((final_size as u64) < u32::MAX as u64);
    for size in 1..=final_size {
        let is_increasing = size % 2 == 1;
        let tgt_row = size - 1;
        let tgt_col = size - 1;
        let size = u32::try_from(size).unwrap();
        if is_increasing {
            let items = ((size - 1)..(size + size - 2)).chain(std::iter::once(0));
            res.set_row(tgt_row, items.clone());
            res.set_col(tgt_col, items);
        } else {
            let items = (0..size).rev();
            res.set_row(tgt_row, items.clone());
            res.set_col(tgt_col, items);
        }
    }
    res
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
    use crate::matrix::{Matrix, MatrixSize};
    use indoc::indoc;
    use similar_asserts::assert_eq;

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
    fn parse_output(n: usize, s: &str) -> Matrix<u32> {
        let lines = s.trim().lines().collect::<Vec<_>>();
        assert_eq!(lines.len(), n);
        Matrix::from_nested_iters(
            MatrixSize::square(n),
            lines
                .iter()
                .map(|line| line.split_whitespace().map(|s| s.parse::<u32>().unwrap())),
        )
    }
}
