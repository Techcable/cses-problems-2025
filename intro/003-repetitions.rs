fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::io::read_to_string(std::io::stdin())?;
    let input = input.trim().to_string();
    println!("{}", longest_run(&input));
    Ok(())
}

fn longest_run(s: &str) -> usize {
    let mut longest_run = 0;
    let mut last = None;
    let mut current_run = 1;
    for c in s.chars() {
        if last == Some(c) {
            current_run += 1;
        } else {
            longest_run = longest_run.max(current_run);
            current_run = 1;
        }
        last = Some(c);
    }
    longest_run.max(current_run)
}

#[cfg(test)]
mod test {
    use super::longest_run;

    #[test]
    fn single_item() {
        assert_eq!(longest_run("A"), 1);
        assert_eq!(longest_run("AA"), 2,);
        assert_eq!(longest_run("AAA"), 3);
    }

    #[test]
    fn example() {
        assert_eq!(longest_run("ATTCGGGA"), 3);
    }
}
