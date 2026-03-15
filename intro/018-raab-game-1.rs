use std::cmp::Ordering;
use std::fmt::{Display, Write};
use std::io::Write as IoWrite;
use std::str::FromStr;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let mut lines = input.lines();
    let num_inputs = lines.next().unwrap().trim().parse::<usize>()?;
    let games = lines
        .map(Game::from_str)
        .collect::<Result<Vec<Game>, _>>()?;
    assert_eq!(num_inputs, games.len());
    let mut stdout = std::io::stdout();
    let mut buffer = String::new();
    for game in games {
        match solve(game) {
            None => println!("NO"),
            Some(Solution { left, right }) => {
                buffer.clear();
                buffer.push_str("YES\n");
                join_into(&left, " ", &mut buffer);
                buffer.push('\n');
                join_into(&right, " ", &mut buffer);
                stdout.write_all(buffer.as_bytes())?;
            }
        }
    }
    Ok(())
}
fn join_into<T: Display>(x: impl IntoIterator<Item = T>, sep: &str, res: &mut String) {
    let mut first = true;
    for item in x {
        if !first {
            res.push_str(sep);
        }
        first = false;
        write!(res, "{item}").unwrap(); // not possible for str
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Solution {
    pub left: Vec<u32>,
    pub right: Vec<u32>,
}
impl From<(&[u32], &[u32])> for Solution {
    fn from(value: (&[u32], &[u32])) -> Self {
        Solution {
            left: value.0.to_vec(),
            right: value.1.to_vec(),
        }
    }
}

pub fn solve(game: Game) -> Option<Solution> {
    assert!(game.n > 0);
    let ties = game.num_ties().ok()?;
    /// Checks that all elements of `left` compare as `expected_ord` against the corresponding elements of `right`
    #[track_caller] // error messages are descriptive enough that this is helpful
    fn verify_comparison(expected_ord: Ordering, expected_len: usize, left: &[u32], right: &[u32]) {
        let ctx = || format!("\nleft = {left:?}\nright = {right:?}");
        assert_eq!(
            left.len(),
            right.len(),
            "mismatched lengths for left, right (expected_len = {expected_len}){ctx}",
            ctx = ctx()
        );
        assert_eq!(
            left.len(),
            expected_len,
            "expected length {expected_len} != left.len = right.len{ctx}",
            ctx = ctx()
        );
        if !cfg!(debug_assertions) {
            return;
        }
        for (a, b) in left.iter().copied().zip(right.iter().copied()) {
            assert_eq!(
                a.cmp(&b),
                expected_ord,
                "expected {a} {expected_ord:?} {b}{ctx}",
                ctx = ctx()
            );
        }
    }
    // there is a pattern the outputs seem to follow:
    // [player 1 loses] [player 2 loses] [ties]
    // as long as the wins add up after ties,
    // we should be able to handle any game
    let non_tied = game.n - ties;
    if game.total_wins() != non_tied {
        return None;
    }
    let Game { a, b, .. } = game;
    // as described in the official analysis page,
    // if exactly one player has zero wins, then no solution is possible.
    // This is an improvement over the previous submission doing an O(n) check for validity
    if matches!((a, b), (0, 1..) | (1.., 0)) {
        return None;
    }
    let mut player1 = Vec::with_capacity(game.n as usize);
    let mut player2 = Vec::with_capacity(game.n as usize);
    // we need to come up with three sequences of pairs x, y, z s.t.
    // x[i].0 < x[i].1
    // y[i].0 > y[i].1
    // z[i].0 == z[i].0
    // with |x|=b, |y|=a, |z|=n-a-b=ties
    // picking z is easy as we just take the highest `ties` numbers
    // for x1 we pick the lowest numbers 1..=b, for x2 we pick (a + 1)..=a+b
    // for y2 we pick the higher numbers (b+1)..=(a+b), for y2 we pick (b+1)..=(a+b)
    for x in 1..=b {
        player1.push(x);
        player2.push(a + x);
    }
    verify_comparison(Ordering::Less, b as usize, &player1, &player2);
    for y in 1..=a {
        player1.push(b + y);
        player2.push(y);
    }
    verify_comparison(
        Ordering::Greater,
        a as usize,
        &player1[b as usize..],
        &player2[b as usize..],
    );
    assert_eq!(player1.len(), non_tied as usize);
    assert_eq!(player2.len(), non_tied as usize);
    for offset in 1..=ties {
        player1.push(non_tied + offset);
        player2.push(non_tied + offset);
    }
    verify_comparison(
        Ordering::Equal,
        ties as usize,
        &player1[non_tied as usize..],
        &player2[non_tied as usize..],
    );
    assert_eq!(player1.len(), game.n as usize);
    assert_eq!(player2.len(), game.n as usize);
    let sol = Solution {
        left: player1,
        right: player2,
    };
    if cfg!(debug_assertions) {
        verify_solution(game, &sol);
    }
    Some(sol)
}
fn verify_solution(game: Game, sol: &Solution) {
    let ties = game.num_ties().unwrap();
    let mut seen1 = vec![false; game.n as usize];
    let mut seen2 = vec![false; game.n as usize];
    assert_eq!(sol.left.len(), game.n as usize);
    assert_eq!(sol.right.len(), game.n as usize);
    let mut win_left = 0u32;
    let mut win_right = 0u32;
    for (&left, &right) in sol.left.iter().zip(&sol.right) {
        assert!(
            !std::mem::replace(&mut seen1[left as usize - 1], true),
            "duplicate {left} in left {sol:?} for {game:?}"
        );
        assert!(
            !std::mem::replace(&mut seen2[right as usize - 1], true),
            "duplicate {right} in right {sol:?} for {game:?}"
        );
        match left.cmp(&right) {
            Ordering::Less => {
                win_right += 1;
            }
            Ordering::Equal => {}
            Ordering::Greater => {
                win_left += 1;
            }
        }
    }
    let actual_ties = game.n - win_left - win_right;
    assert_eq!(
        (win_left, win_right, actual_ties),
        (game.a, game.b, ties),
        "{sol:?} for {game:?}"
    );
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Game {
    /// Number of cards in the game
    pub n: u32,
    pub a: u32,
    pub b: u32,
}
impl Game {
    #[inline]
    pub fn new(n: u32, a: u32, b: u32) -> Game {
        Game { n, a, b }
    }
    #[inline]
    pub fn total_wins(&self) -> u32 {
        self.a + self.b
    }
    #[inline]
    pub fn num_ties(&self) -> Result<u32, TooManyWinsError> {
        self.n
            .checked_sub(self.total_wins())
            .ok_or(TooManyWinsError)
    }
}
/// Indicates that [`Game::num_ties`] cannot be computed because there are too many wins.
#[derive(Debug, Clone, Copy)]
pub struct TooManyWinsError;
impl FromStr for Game {
    type Err = GameParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let entries = s
            .split_whitespace()
            .map(|x| {
                x.parse::<u32>().map_err(|invalid_int| {
                    GameParseError(format!("line has invalid integer, {invalid_int}"))
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        if entries.len() != 3 {
            return Err(GameParseError(format!(
                "expected 3 entries, got {}",
                entries.len()
            )));
        }
        Ok(Game {
            n: entries[0],
            a: entries[1],
            b: entries[2],
        })
    }
}
#[derive(Debug)]
pub struct GameParseError(String);
impl Display for GameParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "failed to parse game: {}", self.0)
    }
}
impl std::error::Error for GameParseError {}

#[cfg(test)]
mod test {
    use super::{solve, Game, Solution};
    use itertools::Itertools;

    #[track_caller]
    fn verify_no_sol(game: Game) {
        assert_eq!(solve(game), None);
    }
    #[track_caller]
    fn verify_sol(game: Game, x: &[u32], y: &[u32]) {
        verify_sol_any(game, [(x, y)]);
    }
    type SolPair<'a> = (&'a [u32], &'a [u32]);
    fn verify_sol_any<const N: usize>(game: Game, possible_solutions: [SolPair; N]) {
        let possible_solutions: [_; N] = possible_solutions
            .iter()
            .copied()
            .map(Solution::from)
            .collect_array::<N>()
            .unwrap();
        let actual_sol = solve(game);
        assert!(
            actual_sol
                .as_ref()
                .is_some_and(|sol| possible_solutions.contains(sol)),
            "solution {actual_sol:?} is not one of the expected solutions {possible_solutions:?}"
        );
    }

    /// Test the official example.
    #[test]
    fn example() {
        verify_sol_any(
            Game::new(4, 1, 2),
            [
                (&[1, 4, 3, 2], &[2, 1, 3, 4]), // official answer
                (&[1, 2, 3, 4], &[2, 3, 1, 4]), // another possibility: win2, win2, win1, tie
            ],
        );
        verify_no_sol(Game::new(2, 0, 1));
        verify_sol(Game::new(3, 0, 0), &[1, 2, 3], &[1, 2, 3]);
        verify_sol(Game::new(2, 1, 1), &[1, 2], &[2, 1]);
        verify_no_sol(Game::new(4, 4, 1));
    }

    /// Test a subset of the full test 1
    ///
    /// The full test has over 800 entries.
    #[test]
    fn test1() {
        verify_sol(Game::new(1, 0, 0), &[1], &[1]);

        verify_no_sol(Game::new(1, 0, 1));
        verify_no_sol(Game::new(1, 1, 0));
        verify_no_sol(Game::new(1, 1, 1));

        verify_sol(Game::new(2, 0, 0), &[1, 2], &[1, 2]);

        verify_no_sol(Game::new(2, 0, 1));
        verify_no_sol(Game::new(2, 0, 2));
        verify_no_sol(Game::new(2, 1, 0));

        verify_sol(Game::new(2, 1, 1), &[1, 2], &[2, 1]);

        verify_no_sol(Game::new(2, 1, 2));
        verify_no_sol(Game::new(2, 2, 0));
        verify_no_sol(Game::new(2, 2, 1));
        verify_no_sol(Game::new(2, 2, 2));

        verify_sol(Game::new(3, 0, 0), &[1, 2, 3], &[1, 2, 3]);

        verify_no_sol(Game::new(3, 0, 1));
        verify_no_sol(Game::new(3, 0, 2));
        verify_no_sol(Game::new(3, 0, 3));
        verify_no_sol(Game::new(3, 1, 0));

        verify_sol(Game::new(3, 1, 1), &[1, 2, 3], &[2, 1, 3]);

        verify_sol(Game::new(3, 1, 2), &[1, 2, 3], &[2, 3, 1]);

        verify_no_sol(Game::new(3, 1, 3));
        verify_no_sol(Game::new(3, 2, 0));

        verify_sol(Game::new(3, 2, 1), &[1, 2, 3], &[3, 1, 2]);

        verify_no_sol(Game::new(3, 2, 2));
        verify_no_sol(Game::new(3, 2, 3));
        verify_no_sol(Game::new(3, 3, 0));
        verify_no_sol(Game::new(3, 3, 1));
        verify_no_sol(Game::new(3, 3, 2));
        verify_no_sol(Game::new(3, 3, 3));

        verify_sol(Game::new(4, 0, 0), &[1, 2, 3, 4], &[1, 2, 3, 4]);

        verify_no_sol(Game::new(4, 0, 1));
        verify_no_sol(Game::new(4, 0, 2));
        verify_no_sol(Game::new(4, 0, 3));
        verify_no_sol(Game::new(4, 0, 4));
        verify_no_sol(Game::new(4, 1, 0));

        verify_sol(Game::new(4, 1, 1), &[1, 2, 3, 4], &[2, 1, 3, 4]);

        verify_sol(Game::new(4, 1, 2), &[1, 2, 3, 4], &[2, 3, 1, 4]);

        verify_sol(Game::new(4, 1, 3), &[1, 2, 3, 4], &[2, 3, 4, 1]);

        verify_no_sol(Game::new(4, 1, 4));
        verify_no_sol(Game::new(4, 2, 0));

        verify_sol(Game::new(4, 2, 1), &[1, 2, 3, 4], &[3, 1, 2, 4]);

        verify_sol(Game::new(4, 2, 2), &[1, 2, 3, 4], &[3, 4, 1, 2]);

        verify_no_sol(Game::new(4, 2, 3));
        verify_no_sol(Game::new(4, 2, 4));
        verify_no_sol(Game::new(4, 3, 0));

        verify_sol(Game::new(4, 3, 1), &[1, 2, 3, 4], &[4, 1, 2, 3]);

        verify_no_sol(Game::new(4, 3, 2));
        verify_no_sol(Game::new(4, 3, 3));
        verify_no_sol(Game::new(4, 3, 4));
        verify_no_sol(Game::new(4, 4, 0));
        verify_no_sol(Game::new(4, 4, 1));
        verify_no_sol(Game::new(4, 4, 2));
        verify_no_sol(Game::new(4, 4, 3));
        verify_no_sol(Game::new(4, 4, 4));

        verify_sol(Game::new(5, 0, 0), &[1, 2, 3, 4, 5], &[1, 2, 3, 4, 5]);

        verify_no_sol(Game::new(5, 0, 1));
        verify_no_sol(Game::new(5, 0, 2));
        verify_no_sol(Game::new(5, 0, 3));
        verify_no_sol(Game::new(5, 0, 4));
        verify_no_sol(Game::new(5, 0, 5));
        verify_no_sol(Game::new(5, 1, 0));

        verify_sol(Game::new(5, 1, 1), &[1, 2, 3, 4, 5], &[2, 1, 3, 4, 5]);

        verify_sol(Game::new(5, 1, 2), &[1, 2, 3, 4, 5], &[2, 3, 1, 4, 5]);

        verify_sol(Game::new(5, 1, 3), &[1, 2, 3, 4, 5], &[2, 3, 4, 1, 5]);

        verify_sol(Game::new(5, 1, 4), &[1, 2, 3, 4, 5], &[2, 3, 4, 5, 1]);

        verify_no_sol(Game::new(5, 1, 5));
        verify_no_sol(Game::new(5, 2, 0));

        verify_sol(Game::new(5, 2, 1), &[1, 2, 3, 4, 5], &[3, 1, 2, 4, 5]);

        verify_sol(Game::new(5, 2, 2), &[1, 2, 3, 4, 5], &[3, 4, 1, 2, 5]);

        verify_sol(Game::new(5, 2, 3), &[1, 2, 3, 4, 5], &[3, 4, 5, 1, 2]);

        verify_no_sol(Game::new(5, 2, 4));
        verify_no_sol(Game::new(5, 2, 5));
        verify_no_sol(Game::new(5, 3, 0));

        verify_sol(Game::new(5, 3, 1), &[1, 2, 3, 4, 5], &[4, 1, 2, 3, 5]);

        verify_sol(Game::new(5, 3, 2), &[1, 2, 3, 4, 5], &[4, 5, 1, 2, 3]);
    }

    /// Test a subset of the full test 2.
    ///
    /// The full test has 1000 entries.
    #[test]
    fn test2() {
        verify_no_sol(Game::new(100, 79, 68));
        verify_no_sol(Game::new(100, 90, 46));
        verify_no_sol(Game::new(100, 73, 74));
        verify_no_sol(Game::new(100, 93, 21));
        verify_no_sol(Game::new(100, 99, 42));
        verify_no_sol(Game::new(100, 49, 81));

        verify_sol(
            Game::new(100, 46, 39),
            &[
                1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44,
                45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65,
                66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86,
                87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100,
            ],
            &[
                47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67,
                68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 1, 2, 3, 4,
                5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
                27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 86,
                87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100,
            ],
        );

        verify_no_sol(Game::new(100, 50, 89));
        verify_no_sol(Game::new(100, 26, 97));
        verify_no_sol(Game::new(100, 84, 46));

        verify_sol(
            Game::new(100, 13, 54),
            &[
                1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44,
                45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65,
                66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86,
                87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100,
            ],
            &[
                14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34,
                35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55,
                56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
                12, 13, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86,
                87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100,
            ],
        );

        verify_no_sol(Game::new(100, 81, 51));

        verify_sol(
            Game::new(100, 8, 64),
            &[
                1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44,
                45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65,
                66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86,
                87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100,
            ],
            &[
                9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
                30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50,
                51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71,
                72, 1, 2, 3, 4, 5, 6, 7, 8, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86,
                87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100,
            ],
        );

        verify_no_sol(Game::new(100, 89, 85));

        verify_sol(
            Game::new(100, 44, 51),
            &[
                1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44,
                45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65,
                66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86,
                87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100,
            ],
            &[
                45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65,
                66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86,
                87, 88, 89, 90, 91, 92, 93, 94, 95, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
                15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
                36, 37, 38, 39, 40, 41, 42, 43, 44, 96, 97, 98, 99, 100,
            ],
        );

        verify_no_sol(Game::new(100, 51, 94));
        verify_no_sol(Game::new(100, 39, 84));

        verify_sol(
            Game::new(100, 2, 45),
            &[
                1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44,
                45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65,
                66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86,
                87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100,
            ],
            &[
                3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
                25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
                46, 47, 1, 2, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64,
                65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85,
                86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100,
            ],
        );
    }
}
