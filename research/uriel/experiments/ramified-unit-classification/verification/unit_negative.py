"""Require the kernel to reject a square root at the positive nonsquare unit."""

import hashlib
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory


SOURCE = """import DilateNear

example : ∃ a b : ZMod 4,
    (⟨a,b⟩ : RamDilate.S 2)^2 = 1+2*QuadraticAlgebra.omega := by
  decide +kernel
"""


def check(compiler, env, work):
    with TemporaryDirectory(dir=work) as directory:
        source = Path(directory) / "PositiveUnitSquareClaim.lean"
        source.write_text(SOURCE, encoding="utf-8")
        result = subprocess.run(
            [str(compiler), source.name], cwd=directory, env=env, check=False,
            capture_output=True, text=True,
        )
    log = result.stdout + result.stderr
    markers = ("proved that the proposition", "is false", "1 + 2 * QuadraticAlgebra.omega")
    if result.returncode == 0 or any(marker not in log for marker in markers):
        raise RuntimeError(f"Unexpected response to false square-root claim:\n{log}")
    return {
        "lean_exit": result.returncode,
        "coefficient_modulus": 4,
        "unit_coefficients": [1, 2],
        "source_sha256": hashlib.sha256(SOURCE.encode()).hexdigest(),
    }
