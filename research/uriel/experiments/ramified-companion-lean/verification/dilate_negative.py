"""Change the target-16 certificate by one solution and require Lean's arithmetic rejection."""
import argparse
import hashlib
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

SOURCE = """import RamBase

example : TargetOne.count 6 (16 : RamBase.R) = 65537 * 2^35 + 1 := by
  rw [RamBase.census_six]
  decide +kernel
"""


def check(compiler, env, work):
    """Reject a missing import, an elaboration failure, or an unexpected acceptance."""
    with TemporaryDirectory(dir=work) as directory:
        source = Path(directory) / 'TargetSixteenOneCount.lean'
        source.write_text(SOURCE, encoding='utf-8')
        proc = subprocess.run([str(compiler), source.name], cwd=directory, env=env,
                              capture_output=True, text=True, check=False)
    log = proc.stdout + proc.stderr
    markers = ('proved that the proposition', 'is false', '65537 * 2 ^ 35 + 1')
    if proc.returncode == 0 or any(marker not in log for marker in markers):
        raise RuntimeError(f'Unexpected response to target-16 perturbation:\n{log}')
    return {
        'target': 16,
        'coefficient_depth': 5,
        'expected_count': 65537 * 2**35,
        'changed_numerator_by': 1,
        'lean_exit': proc.returncode,
        'source_sha256': hashlib.sha256(SOURCE.encode('utf-8')).hexdigest(),
        'reason': 'Lean reduced the one-extra-solution equality to false',
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', required=True, type=Path)
    parser.add_argument('--work', default=Path('.'), type=Path)
    args = parser.parse_args()
    print(check(args.lean.resolve(), os.environ.copy(), args.work.resolve()))
