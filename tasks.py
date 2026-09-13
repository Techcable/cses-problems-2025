import os
import sys

from invoke import Collection, task

HAS_COLORS: bool = (sys.stderr.isatty() or os.getenv("FORCE_COLOR")) and not os.getenv("NO_COLOR")


def apply_colors(msg: object, /, *, code: str) -> str:
    if HAS_COLORS:
        return f"\x1b[{code}m{msg}\x1b[0m"
    else:
        return str(msg)


def log_info(msg: object):
    print(
        apply_colors("INFO:", code="1;32"),
        apply_colors(msg, code="1"),
    )


@task
def test(ctx):
    check(ctx, format=False)
    ctx.run("cargo nextest run --workspace")
    # needed because nextest doesn't support doctests
    ctx.run("cargo test --doc --workspace")
    run_format(ctx, check=True)


@task
def check(ctx, format=True):
    clippy(ctx)
    msrv(ctx)
    ctx.run("cargo doc --document-private-items --no-deps --workspace --all-features")
    # by default, check formatting as well
    if format:
        run_format(ctx, check=True)


@task
def msrv(ctx):
    """Verify that the code compiles on the MSRV"""
    ctx.run("cargo +1.75 check --workspace")


@task
def clippy(ctx):
    ctx.run("cargo clippy --workspace --all-targets")


@task(name="format")
def run_format(ctx, check=False):
    verb = "Checking" if check else "Fixing"
    log_info(f"{verb} formatting")
    maybe_check = " --check" if check else ""
    maybe_fix = " --fix" if not check else ""
    ctx.run("cargo +nightly fmt --all" + maybe_check)
    ctx.run("tombi format" + maybe_check)

    # need python format for invoke.py
    ctx.run("ruff format" + maybe_check)
    ctx.run("ruff check --select=I" + maybe_fix)  # works like isort
    check_spelling(ctx, fix=False)


TYPOS_VER = "1.50.1"  # pinned to avoid update breakage


@task(name="typos")
def check_spelling(ctx, fix=False):
    maybe_write = " --write-changes" if fix else ""
    ctx.run(f"uvx typos@{TYPOS_VER}" + maybe_write)


ns = Collection(test, check, clippy, msrv, run_format, check_spelling)
ns.configure(
    {
        "run": {
            "echo": True,
            "env": {
                "FORCE_COLOR": "1" if HAS_COLORS else "",
                "CARGO_TERM_COLOR": "always" if HAS_COLORS else "never",
                # workaround mitsuhiko/similar-asserts#10 (right now FORCE_COLOR doesn't work)
                "CLICOLOR_FORCE": "1" if HAS_COLORS else "",
            },
        }
    }
)
