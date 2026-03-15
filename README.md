cses-problems-2025
==================
My solutions to the [CSES Problem Set] in Rust

Split into different crates for the different categories.

Originally inspired to do this from [matklad's blog post](https://matklad.github.io/2023/08/06/fantastic-learning-resources.html).

See this "howto" guide for various details: <https://cses.fi/howto/>

[CSES Problem Set]: https://cses.fi/problemset/

## Rust Environment
CSES uses the relatively modern Rust 1.75, as described in their [howto](https://cses.fi/howto) guide.

The only included package is `rand = "0.8.4"`.
To ensure compatibility with Rust 1.75, we run `cargo check` on that version.

Tests are disabled by `#[cfg(test)]` so can use newer rust features and additional libraries.
In particular, we include `itertools` which is extremely useful.
