check:
    typos
    cargo clippy --workspace --all

format:
    cargo fmt --all
    typos
