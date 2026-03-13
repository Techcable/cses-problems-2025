use std::fmt::Display;
use std::str::FromStr;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let mut lines = input.lines();
    let num_inputs = lines.next().unwrap().trim().parse::<usize>()?;
    let games = lines
        .map(Game::from_str)
        .collect::<Result<Vec<Game>, _>>()?;
}

pub struct Game {
    pub num_cards: usize,
    pub scores: [usize; 2],
}
impl Game {
    #[inline]
    pub fn total_wins(&self) -> usize {
        self.scores.iter().copied().sum()
    }
    #[inline]
    pub fn num_ties(&self) -> Result<usize, TooManyWinsError> {
        self.num_cards
            .checked_sub(self.total_wins())
            .ok_or(TooManyWinsError)
    }
}
/// Indicates that [Game::num_ties()] cannot be computed because there are too many wins.
#[derive(Debug, Clone, Copy)]
pub struct TooManyWinsError;
impl FromStr for Game {
    type Err = GameParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let entries = s
            .split_whitespace()
            .map(|x| {
                x.parse::<usize>().map_err(|invalid_int| {
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
            num_cards: entries[0],
            scores: [entries[1], entries[2]],
        })
    }
}
#[derive(Debug)]
struct GameParseError(String);
impl Display for GameParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "failed to parse game: {}", self.0)
    }
}
impl std::error::Error for GameParseError {}

#[cfg(test)]
mod test {
    use super::Game;

    impl Game {
        pub fn new(n: usize, a: usize, b: usize) -> Game {
            Game {
                num_cards: n,
                scores: [a, b],
            }
        }
    }
    fn verify_no_sol(game: Game) {
        todo!()
    }
    fn verify_sol(game: Game, x: &[usize], y: &[usize]) {
        todo!()
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
