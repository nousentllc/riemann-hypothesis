"""Require kernel evaluation to reject the square count at the companion target."""

import hashlib
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory


SOURCE = """import DilateLowCompanion

open RamDilate TargetOne
example : count 6 ((4 : RamField.R 3) * (1 + QuadraticAlgebra.omega)) = 2155872256 := by
  rw [low3_four_companion]
  decide +kernel
"""


def check(compiler, env, work):
    """Fail if Lean accepts the wrong sign or cannot reach the arithmetic check."""
    with TemporaryDirectory(dir=work) as directory:
        source = Path(directory) / "CompanionWrongSign.lean"
        source.write_text(SOURCE, encoding="utf-8")
        result = subprocess.run(
            [str(compiler), source.name], cwd=directory, env=env,
            capture_output=True, text=True, check=False,
        )
    log = result.stdout + result.stderr
    markers = ("proved that the proposition", "is false", "2155872256")
    if result.returncode == 0 or any(marker not in log for marker in markers):
        raise RuntimeError(f"Unexpected response to companion wrong-sign control:\n{log}")
    return {
        "lean_exit": result.returncode,
        "companion_count": 2139095040,
        "rejected_square_count": 2155872256,
        "source_sha256": hashlib.sha256(SOURCE.encode()).hexdigest(),
    }
