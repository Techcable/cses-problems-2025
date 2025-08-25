check:
    typos
    cargo clippy --workspace --all

format:
    cargo fmt --all
    typos

test:
    cargo clippy --all
    cargo test --all
