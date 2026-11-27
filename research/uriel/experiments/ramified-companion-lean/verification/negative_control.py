"""Check that Lean rejects the one-count perturbation for the intended reason."""
from pathlib import Path
from tempfile import TemporaryDirectory
import os
import subprocess

SOURCE = """import RamBase
open RamBase
example : TargetOne.count 6 (4 : R) = 257*2^43+1 := by
  rw [census_six]
  decide +kernel
"""


def check(compiler, env, work):
    with TemporaryDirectory(dir=work) as d:
        path = Path(d)/'OneCountPerturbation.lean'
        path.write_text(SOURCE, encoding='utf-8')
        res = subprocess.run([str(compiler), path.name], cwd=d, env=env,
                             capture_output=True, text=True, check=False)
        log = res.stdout + res.stderr
        if (res.returncode == 0 or 'proved that the proposition' not in log
            or 'is false' not in log or '257 * 2 ^ 43 + 1' not in log):
            raise RuntimeError(log)
        return {'lean_exit':res.returncode, 'changed_numerator_by':1,
                'reason':'Lean reduced the proposed successor equality to false'}


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', required=True, type=Path)
    parser.add_argument('--work', default=Path('.'), type=Path)
    args = parser.parse_args()
    print(check(args.lean.resolve(), os.environ.copy(), args.work.resolve()))
