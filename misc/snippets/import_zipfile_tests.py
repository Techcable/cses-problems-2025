## Snippet not intended for direct ececution

import zipfile
import textwrap
from itertools import islice

INDENT: str = ' ' * 4

def indent(x: str, /, level: int) -> str:
    indent = INDENT * level
    return '\n'.join([indent + line for line in x.splitlines()])

def print_test_intro_016(target_zipfile_path: str, num_tests: int):
    target_zipfile = zipfile.ZipFile(target_zipfile_path)
    joined = []
    for idx in range(1, num_tests + 1):
        rawin = target_zipfile.read(f'{idx}.in').decode('utf8')
        rawout = target_zipfile.read(f'{idx}.out').decode('utf8')
        inlines = rawin.strip().splitlines()
        assert len(inlines) == 2, inlines
        input_vals = ', '.join(inlines[1].split())
        joined.append(textwrap.dedent(f"""
            #[test]
            fn test{idx}() {{
            verify([{input_vals}], {rawout.strip()});
            }}
            """))
    print('\n'.join(joined))


def print_test_intro_018(target_zipfile_path: str, num_tests: int, *, limit: int | None = None):
    type Game = tuple[int, int, int]
    type Solution = tuple[list[int], list[int]]

    def parse_game(line: str) -> Game:
        res = tuple(map(int, line.split()))
        assert len(res) == 3, line
        return res  # type: ignore

    target_zipfile = zipfile.ZipFile(target_zipfile_path)
    joined = []
    for idx in range(1, num_tests + 1):
        rawin = target_zipfile.read(f'{idx}.in').decode('utf8')
        rawout = target_zipfile.read(f'{idx}.out').decode('utf8')
        inlines = rawin.strip().splitlines()
        outlines = rawout.strip().splitlines()
        num_inputs = int(inlines.pop(0))
        input_games = [tuple(map(int, line.split())) for line in inlines]
        assert all(len(x) == 3 for x in input_games)
        assert len(input_games) == num_inputs
        outputs: list[Solution | None] = []
        while outlines:
            match outlines.pop(0):
                case 'NO':
                    outputs.append(None)
                case 'YES':
                    first = list(map(int, outlines.pop(0).split()))
                    second = list(map(int, outlines.pop(0).split()))
                    assert len(first) == len(second)
                    outputs.append((first, second))
                case other:
                    raise AssertionError(other)
        assert len(input_games) == len(outputs)
        test_statements = []
        for game, output in islice(zip(input_games, outputs, strict=True), limit):
            n, a, b = game
            game = f"Game::new({n}, {a}, {b})"
            if output is None:
                test_statements.append(f"verify_no_sol({game});")
                continue
            test_statements.append(textwrap.dedent(f"""
                verify_sol(
                    {game},
                    &[{', '.join(map(str, output[0]))}],
                    &[{', '.join(map(str, output[1]))}],
                );
                """
            ))
        body = indent('\n'.join(test_statements), 1)
        joined.append(textwrap.dedent(f"""
            #[test]
            fn test{idx}() {{
                {body}
            }}
            """))
    print(indent('\n'.join(joined), 2))
