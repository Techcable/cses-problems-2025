#![allow(clippy::empty_line_after_doc_comments)]
use std::ops::Sub;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let mut lines = input.lines();
    let test_count = lines.next().unwrap().trim().parse::<usize>()?;
    let tests = lines
        .map(|x| {
            let mut parts = x.split_whitespace();
            let x = parts.next().unwrap().parse::<u32>().unwrap();
            let y = parts.next().unwrap().parse::<u32>().unwrap();
            assert_eq!(parts.next(), None);
            Pos::from_input(x, y)
        })
        .collect::<Vec<_>>();
    assert_eq!(test_count, tests.len());
    for test in tests {
        println!("{}", value_at(test));
    }
    Ok(())
}

fn value_at(target: Pos) -> u64 {
    let radius = target.radius();
    let start = radius.start();
    let (start, target) = match radius.direction() {
        SpiralDir::Clockwise => (start, target),
        SpiralDir::CounterClockwise => (
            SpiralEntry {
                pos: start.pos.transpose(),
                value: start.value,
            },
            target.transpose(),
        ),
    };
    // can assume clockwise from here
    assert_eq!(start.pos.row(), 0, "not clockwise: start should be at top");
    if target.row() < radius.index() {
        assert_eq!(target.column(), radius.index());
        start.value + target.row() as u64
    } else {
        assert_eq!(target.row(), radius.index());
        assert!(target.column() <= radius.index());
        radius.corner_value() + (radius.index() - target.column()) as u64
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SpiralEntry {
    value: u64,
    pos: Pos,
}
impl SpiralEntry {
    /// The first entry in the spiral.
    pub const START: Self = SpiralEntry {
        value: 1,
        pos: Pos(0, 0),
    };
}

/// The `(row, column)` position within a spiral (zero-based)
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Pos(u32, u32);
impl Pos {
    /// The radius of the spiral this value is contained in.
    #[inline]
    pub fn radius(self) -> Radius {
        Radius(self.0.max(self.1) + 1).validate()
    }

    #[inline]
    pub fn transpose(self) -> Pos {
        Pos(self.1, self.0)
    }

    #[inline]
    pub fn row(self) -> u32 {
        self.0
    }

    #[inline]
    pub fn column(self) -> u32 {
        self.1
    }

    #[inline]
    fn from_input(row: u32, col: u32) -> Self {
        Pos(row - 1, col - 1)
    }
}

/// The direction of a spiral
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum SpiralDir {
    Clockwise,
    CounterClockwise,
}

/// The maximum input allowed by the test (inclusive)
pub const MAX_INPUT: u32 = 10u32.pow(9);
/// The valid inputs allowed by the test

/// The radius of a fixed-size spiral (one-based).
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct Radius(u32);
impl Radius {
    /// The zero-based index corresponding to this radius
    #[inline]
    pub fn index(self) -> u32 {
        self.0 - 1
    }

    #[inline]
    #[track_caller]
    fn validate(self) -> Self {
        assert!(self.0 > 0, "invalid radius");
        self
    }

    #[inline]
    pub fn start_value(self) -> u64 {
        self.validate();
        if self.0 == 1 {
            1
        } else {
            (self - 1).end_value() + 1
        }
    }

    #[inline]
    pub fn end_value(self) -> u64 {
        self.validate();
        // 1x1 checkerboard - 1 entry
        // 2x2 checkerboard - 4 entries
        // 3x3 checkerboard - 9 entries
        // etc...
        //
        // (u32::MAX as u64) * (u32::MAX as u64) does not overflow
        (self.0 as u64) * (self.0 as u64)
    }

    #[inline]
    pub fn direction(self) -> SpiralDir {
        if self.0 % 2 == 0 {
            SpiralDir::Clockwise
        } else {
            SpiralDir::CounterClockwise
        }
    }

    /// Finds the start of this radius,
    /// one past the end of the previous one.
    pub fn start(self) -> SpiralEntry {
        self.validate();
        let value = self.start_value();
        let pos = self.end_pos().transpose();
        SpiralEntry { value, pos }
    }

    #[inline]
    pub fn corner_value(&self) -> u64 {
        self.start_value() + self.index() as u64
    }

    /// Finds the outer corner for this radius
    pub fn corner(self) -> SpiralEntry {
        self.validate();
        SpiralEntry {
            value: self.corner_value(),
            pos: Pos(self.index(), self.index()),
        }
    }

    #[inline]
    fn end_pos(self) -> Pos {
        self.validate();
        let clockwise = Pos(self.index(), 0);
        match self.direction() {
            SpiralDir::Clockwise => clockwise,
            SpiralDir::CounterClockwise => clockwise.transpose(),
        }
    }

    /// Finds the largest value for the of a spiral of specified radius.
    pub fn end(self) -> SpiralEntry {
        self.validate();
        let value = self.end_value();
        SpiralEntry {
            value,
            pos: self.end_pos(),
        }
    }
}
impl Sub<u32> for Radius {
    type Output = Self;

    #[track_caller]
    #[inline]
    fn sub(self, rhs: u32) -> Self::Output {
        self.0
            .checked_sub(rhs)
            .filter(|&x| x >= 1)
            .map(Radius)
            .expect("subtraction overflow")
    }
}

#[cfg(test)]
mod test {
    #![allow(clippy::pedantic, clippy::all)] // already submitted & written before clippy was run with --tests
    use super::*;

    #[test]
    fn example() {
        assert_eq!(value_at(Pos::from_input(2, 3)), 8);
        assert_eq!(value_at(Pos::from_input(1, 1)), 1);
        assert_eq!(value_at(Pos::from_input(4, 2)), 15);
    }

    #[test]
    fn basic() {
        assert_eq!(value_at(Pos::from_input(5, 5)), 21);
        assert_eq!(value_at(Pos::from_input(3, 5)), 23);
        assert_eq!(value_at(Pos::from_input(5, 3)), 19);
    }

    #[test]
    fn official_2() {
        // it's just this repeated 100_000 times
        assert_eq!(
            value_at(Pos::from_input(1000000000, 1000000000)),
            999999999000000001
        );
    }

    #[test]
    fn pos_radius() {
        assert_eq!(Pos(0, 0).radius(), Radius(1));
        assert_eq!(Pos(0, 3).radius(), Radius(4));
    }

    /// Tests the start/end/corner are correct for the r=1 through r=5.
    #[test]
    fn known_radius_entries() {
        assert_eq!(Radius(1).start(), SpiralEntry::START);
        assert_eq!(Radius(1).corner(), SpiralEntry::START);
        assert_eq!(Radius(1).end(), SpiralEntry::START);
        assert_eq!(
            Radius(2).start(),
            SpiralEntry {
                pos: Pos(0, 1),
                value: 2
            }
        );
        assert_eq!(
            Radius(2).corner(),
            SpiralEntry {
                pos: Pos(1, 1),
                value: 3,
            }
        );
        assert_eq!(
            Radius(2).end(),
            SpiralEntry {
                pos: Pos(1, 0),
                value: 4
            }
        );
        assert_eq!(
            Radius(3).start(),
            SpiralEntry {
                pos: Pos(2, 0),
                value: 5
            }
        );
        assert_eq!(
            Radius(3).corner(),
            SpiralEntry {
                pos: Pos(2, 2),
                value: 7
            }
        );
        assert_eq!(
            Radius(3).end(),
            SpiralEntry {
                pos: Pos(0, 2),
                value: 9
            }
        );
        assert_eq!(
            Radius(4).start(),
            SpiralEntry {
                pos: Pos(0, 3),
                value: 10,
            }
        );
        assert_eq!(
            Radius(4).corner(),
            SpiralEntry {
                pos: Pos(3, 3),
                value: 13,
            }
        );
        assert_eq!(
            Radius(4).end(),
            SpiralEntry {
                pos: Pos(3, 0),
                value: 16,
            }
        );
        assert_eq!(
            Radius(5).start(),
            SpiralEntry {
                pos: Pos(4, 0),
                value: 17,
            }
        );
        assert_eq!(
            Radius(5).corner(),
            SpiralEntry {
                pos: Pos(4, 4),
                value: 21,
            }
        );
        assert_eq!(
            Radius(5).end(),
            SpiralEntry {
                pos: Pos(0, 4),
                value: 25,
            }
        );
    }
}
