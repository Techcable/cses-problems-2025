check: _check && check-format

# just runs checks without checking formatting
#
# used for test action
_check: && msrv
    cargo clippy --workspace --all --tests

# Verify that the code compiles on the MSRV
msrv:
    cargo +1.75 check --workspace

format:
    cargo fmt --all
    typos

check-format:
    cargo fmt --check --all
    typos

test: && _check check-format
    cargo nextest run --all
