check: && check-format
    cargo clippy --workspace --all

format:
    cargo fmt --all
    typos

check-format:
    cargo fmt --check --all
    typos

test: && check-format
    cargo clippy --all
    cargo nextest run --all
