check: _check && check-format

# just runs checks without checking formatting
#
# used for test action
_check:
    cargo clippy --workspace --all --tests

format:
    cargo fmt --all
    typos

check-format:
    cargo fmt --check --all
    typos

test: _check && check-format
    cargo nextest run --all
