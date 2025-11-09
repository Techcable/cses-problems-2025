use std::collections::HashSet;
use std::fmt::{Debug, Display, Formatter};

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let input = input.trim().parse::<u32>()?;
    let result = naive_problem(input);
    println!("{}", result.len());
    for &x in &result {
        println!("{}", x.cses_output());
    }
    Ok(())
}

pub fn naive_problem(n: u32) -> Vec<Action> {
    fn possible_actions() -> impl Iterator<Item = Action> {
        Stack::ALL
            .into_iter()
            .flat_map(|src| Stack::ALL.into_iter().map(move |dest| Action { src, dest }))
            .filter(|action| action.src != action.dest)
    }
    struct SearchState {
        tower: TowerHanoi,
        actions: Vec<Action>,
        level: usize,
    }
    fn maybe_apply<R>(
        state: &mut SearchState,
        action: Action,
        func: impl FnOnce(&mut SearchState) -> R,
    ) -> Result<R, InvalidActionError> {
        state.tower.try_apply(action)?;
        state.actions.push(action);
        let res = func(state);
        assert_eq!(state.actions.pop(), Some(action));
        state.tower.force_apply(action.reverse());
        Ok(res)
    }
    fn naive_search(state: &mut SearchState) -> Option<Vec<Action>> {
        if state.actions.len() >= state.level {
            return None;
        }
        let next_level = state.actions.len() + 1;
        if next_level == state.level {
            // search by adding one additional item
            let mut this_search_level = possible_actions().filter_map(|action| {
                maybe_apply(state, action, |state| {
                    if state.tower.is_complete() {
                        state.tower.validate().expect("tower complete but invalid");
                        assert_eq!(state.actions.len(), state.level);
                        Some(state.actions.clone())
                    } else {
                        None
                    }
                })
                .ok()
                .flatten()
            });
            this_search_level.next()
        } else {
            // need to go deeper than one level
            let mut recursive_search = possible_actions()
                .filter_map(|action| maybe_apply(state, action, naive_search).ok().flatten());
            recursive_search.next()
        }
    }
    const MAX_LEVEL: usize = 500;
    for level in 1..=MAX_LEVEL {
        let mut state = SearchState {
            actions: Vec::new(),
            tower: TowerHanoi::with_size(n),
            level,
        };
        if let Some(res) = naive_search(&mut state) {
            return res;
        }
    }
    panic!("Failed to solve power for n={n} (is MAX_LEVEL={MAX_LEVEL} too low?)")
}
/// The tower of Hanoi.
///
/// Unless [`Self::force_apply`] is called, this only permits legal moves.
#[derive(Clone)]
pub struct TowerHanoi {
    stacks: [Vec<Disk>; 3],
    size: u32,
}
impl TowerHanoi {
    fn disks_for_size(size: u32) -> impl Iterator<Item = Disk> {
        (0..size).rev().map(Disk)
    }
    pub fn with_size(size: u32) -> TowerHanoi {
        TowerHanoi {
            stacks: [Self::disks_for_size(size).collect(), Vec::new(), Vec::new()],
            size,
        }
    }
    pub fn is_complete(&self) -> bool {
        self.stacks[0].is_empty() && self.stacks[1].is_empty()
    }
    pub fn try_apply(&mut self, action: Action) -> Result<(), InvalidActionError> {
        assert_ne!(action.src, action.dest);
        let src_disk = self.stacks[action.src as usize]
            .last()
            .copied()
            .ok_or(InvalidActionError::EmptySource { action })?;
        if let Some(&dest_top) = self.stacks[action.dest as usize].last() {
            assert_ne!(src_disk, dest_top, "Invalid tower due to duplicate disk");
            if src_disk > dest_top {
                return Err(InvalidActionError::LargerOntoSmaller {
                    action,
                    dest_top,
                    src_disk,
                });
            }
        }
        assert_eq!(self.stacks[action.src as usize].pop(), Some(src_disk));
        self.stacks[action.dest as usize].push(src_disk);
        Ok(())
    }
    #[track_caller]
    pub fn force_apply(&mut self, action: Action) {
        let disk = self.stacks[action.src as usize]
            .pop()
            .unwrap_or_else(|| panic!("Empty source for {action}"));
        self.stacks[action.dest as usize].push(disk);
    }
    pub fn validate(&self) -> Result<(), ValidationError> {
        // first check for duplicates and missing disks
        {
            let mut seen = HashSet::new();
            let expected = Self::disks_for_size(self.size).collect::<HashSet<_>>();
            for stack in Stack::ALL {
                for &disk in &self.stacks[stack as usize] {
                    if !seen.insert(disk) {
                        return Err(ValidationError::DuplicateDisk { disk });
                    }
                    if !expected.contains(&disk) {
                        return Err(ValidationError::InvalidDisk {
                            disk,
                            size: self.size,
                        });
                    }
                }
            }
            let missing = &expected - &seen;
            if let Some(smallest_missing) = missing.iter().copied().min() {
                return Err(ValidationError::MissingDisk {
                    size: self.size,
                    disk: smallest_missing,
                });
            }
            assert!(missing.is_empty());
            assert_eq!(
                self.stacks.iter().map(Vec::len).sum::<usize>(),
                self.size as usize
            );
        }
        // now check ordering
        for stack in Stack::ALL {
            let disks = &self.stacks[stack as usize];
            if disks.is_empty() {
                continue;
            }
            let mut last = *disks.first().unwrap();
            for &disk in &disks[1..] {
                if last <= disk {
                    return Err(ValidationError::OutOfOrder {
                        stack,
                        pair: [last, disk],
                    });
                }
                last = disk;
            }
        }
        Ok(())
    }
}
impl Debug for TowerHanoi {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TowerHanoi")
            .field("size", &self.size)
            .field("left", &self.stacks[0])
            .field("middle", &self.stacks[1])
            .field("right", &self.stacks[2])
            .finish()
    }
}
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ValidationError {
    OutOfOrder { stack: Stack, pair: [Disk; 2] },
    DuplicateDisk { disk: Disk },
    MissingDisk { disk: Disk, size: u32 },
    InvalidDisk { disk: Disk, size: u32 },
}
impl Display for ValidationError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match *self {
            ValidationError::OutOfOrder {
                stack,
                pair: [a, b],
            } => {
                write!(f, "{stack} stack out of order, has {a} below {b}")
            }
            ValidationError::DuplicateDisk { disk } => {
                write!(f, "Disk of size {} occurs multiple times", disk.0)
            }
            ValidationError::MissingDisk { disk, size } => {
                write!(
                    f,
                    "Disk of size {} is missing from tower of size {size}",
                    disk.0
                )
            }
            ValidationError::InvalidDisk { disk, size } => {
                write!(
                    f,
                    "Disk of size {} does not belong in tower of size {size}",
                    disk.0
                )
            }
        }
    }
}
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum InvalidActionError {
    LargerOntoSmaller {
        action: Action,
        src_disk: Disk,
        dest_top: Disk,
    },
    EmptySource {
        action: Action,
    },
}
impl InvalidActionError {
    fn action(&self) -> Action {
        match *self {
            InvalidActionError::LargerOntoSmaller { action, .. }
            | InvalidActionError::EmptySource { action, .. } => action,
        }
    }
}
impl Display for InvalidActionError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Failed to move {}: ", self.action())?;
        match *self {
            InvalidActionError::LargerOntoSmaller {
                action: _,
                src_disk,
                dest_top,
            } => {
                write!(
                    f,
                    "would place a size {src_disk} disk on a size {dest_top} disk",
                )
            }
            InvalidActionError::EmptySource { action } => {
                write!(f, "{} is empty", action.src)
            }
        }
    }
}
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Disk(u32);
impl Debug for Disk {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // Strip Disk(..) wrapper as unhelpful
        write!(f, "{}", self.0)
    }
}
impl Display for Disk {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Stack {
    Left,
    Middle,
    Right,
}
impl Stack {
    const ALL: [Stack; 3] = [Stack::Left, Stack::Middle, Stack::Right];
}
impl Display for Stack {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Stack::Left => f.write_str("left"),
            Stack::Middle => f.write_str("middle"),
            Stack::Right => f.write_str("right"),
        }
    }
}
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Action {
    pub src: Stack,
    pub dest: Stack,
}
impl Action {
    pub fn reverse(&self) -> Action {
        Action {
            dest: self.src,
            src: self.dest,
        }
    }
    /// Format this action in the way expected by CSES.
    pub fn cses_output(&self) -> impl Display {
        struct CsesFormat(Action);
        impl Display for CsesFormat {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                write!(
                    f,
                    "{} {}",
                    self.0.src as usize + 1,
                    self.0.dest as usize + 1
                )
            }
        }
        CsesFormat(*self)
    }
}
impl Display for Action {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} to {}", self.src, self.dest)
    }
}
impl Debug for Action {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Action")
            .field(&self.src)
            .field(&self.dest)
            .finish()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    const EXAMPLE_ACTIONS: [Action; 3] = [
        Action {
            src: Stack::Left,
            dest: Stack::Middle,
        },
        Action {
            src: Stack::Left,
            dest: Stack::Right,
        },
        Action {
            src: Stack::Middle,
            dest: Stack::Right,
        },
    ];

    #[test]
    fn example_naive() {
        assert_eq!(naive_problem(2), EXAMPLE_ACTIONS.to_vec());
    }

    #[test]
    fn tower_accepts_example() {
        let mut tower = TowerHanoi::with_size(2);
        for act in EXAMPLE_ACTIONS {
            tower.try_apply(act).unwrap();
        }
        assert!(tower.is_complete());
    }
}
