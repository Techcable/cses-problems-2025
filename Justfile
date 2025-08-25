check: && check-format
    cargo clippy --workspace --all

format:
    cargo fmt --all
    typos

check-format:
    cargo fmt --all
    typos

test: && check-format
    cargo clippy --all
    cargo test --all
