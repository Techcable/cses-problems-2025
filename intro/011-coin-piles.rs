use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{HashMap, VecDeque};
use std::hash::Hash;
use std::str::FromStr;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let mut lines = input.lines();
    let num_inputs = lines.next().unwrap().trim().parse::<usize>()?;
    let inputs = lines
        .map(|line| {
            let entries = line
                .split_whitespace()
                .map(u32::from_str)
                .collect::<Result<Vec<_>, _>>()?;
            assert_eq!(entries.len(), 2);
            Ok((entries[0], entries[1]))
        })
        .collect::<Result<Vec<_>, Box<dyn std::error::Error>>>()?;
    assert_eq!(inputs.len(), num_inputs);
    for (a, b) in inputs {
        println!("{}", if problem(a, b) { "YES" } else { "NO" });
    }
    Ok(())
}

pub const MAX_INPUT: u32 = 10u32.pow(9);
const SMALL_INPUT_BOUND: u32 = 16;
pub fn problem(a: u32, b: u32) -> bool {
    // Impossible to succeed when one input is more than double another
    // that is because the most aggressively we can take from `a` is -2, -1 each time.
    // On the other hand, we are guaranteed to succeed when one input is exactly another
    //
    // After this reduction, max(a, b) < 2 * min(a, b) < 2 * SMALL_INPUT_BOUND
    let min_input = a.min(b);
    let max_input = a.max(b);
    match max_input.cmp(&(min_input * 2)) {
        Ordering::Greater => return false,
        Ordering::Equal => return true,
        Ordering::Less => {} // continue
    }
    memoized_problem(a, b)
}
/// A LRU-like cache, evicting least recently accessed entries.
struct LruCache<K: Eq + Hash + Clone, V> {
    map: HashMap<K, V>,
    inserted_entries: VecDeque<K>,
    capacity: usize,
}
impl<K: Eq + Hash + Clone, V> LruCache<K, V> {
    pub fn with_capacity(capacity: usize) -> LruCache<K, V> {
        LruCache {
            map: HashMap::new(),
            inserted_entries: VecDeque::new(),
            capacity,
        }
    }
    pub fn get(&self, key: &K) -> Option<&V> {
        self.map.get(key)
    }
    pub fn insert(&mut self, key: K, value: V) {
        assert_eq!(self.map.len(), self.inserted_entries.len());
        let old_entry = self.map.insert(key.clone(), value);
        if old_entry.is_none() {
            self.inserted_entries.push_back(key);
        }
        if self.map.len() > self.capacity {
            let evict = self.inserted_entries.pop_front().unwrap();
            let res = self.map.remove(&evict);
            assert!(res.is_some(), "entry in queue but not in map");
        }
    }
}
thread_local! {
    static CACHE: RefCell<LruCache<(u32, u32), bool>> = RefCell::new(LruCache::with_capacity(100_000));
}
pub fn memoized_problem(a: u32, b: u32) -> bool {
    do_search(a, b, |a, b| {
        CACHE.with(|cache| {
            let lock = cache.borrow();
            lock.get(&(a, b)).copied().unwrap_or_else(move || {
                drop(lock);
                let res = memoized_problem(a, b);
                let mut lock = cache.borrow_mut();
                lock.insert((a, b), res);
                drop(lock);
                res
            })
        })
    })
}

pub fn naive_problem(a: u32, b: u32) -> bool {
    do_search(a, b, naive_problem)
}
#[inline]
fn do_search(a: u32, b: u32, subproblem: impl Fn(u32, u32) -> bool) -> bool {
    if a == 0 || b == 0 {
        a == 0 && b == 0
    } else {
        (a > 1 && subproblem(a - 2, b - 1)) || (b > 1 && subproblem(a - 1, b - 2))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn naive_example() {
        assert!(naive_problem(2, 1));
        assert!(!naive_problem(2, 2));
        assert!(naive_problem(3, 3));
    }

    #[test]
    fn example() {
        assert!(problem(2, 1));
        assert!(!problem(2, 2));
        assert!(problem(3, 3));
    }

    #[test]
    fn timeout_max_input() {
        let _ = problem(MAX_INPUT, MAX_INPUT);
    }

    #[test]
    fn test1_small_failures() {
        #[track_caller]
        fn require_yes(a: u32, b: u32) {
            assert!(
                problem(a, b),
                "problem({a}, {b}) should be `YES` (naive_problem is {})",
                if naive_problem(a, b) { "YES" } else { "NO" }
            );
        }
        require_yes(22, 41);
        require_yes(19, 35);
        require_yes(19, 38);
        require_yes(18, 36);
        require_yes(17, 34);
    }
}
