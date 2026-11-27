"""Compile and replay the local assessment controls with the experiment's pinned environment."""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / "riemann-experiments/research/uriel/experiments/second"))
from formal import FLAGS, LEAN, MATHLIB, environment


def run(tc, mathlib):
    env, _ = environment(tc, mathlib)
    modules = {
        "SevenBase": {"SlotSevenProbe.seven_pid", "SlotSevenProbe.base_class_number"},
        "Uniformity": {"WindowUniformity.moving_constants", "WindowUniformity.no_late_windows"},
        "DensityGate": {"DensityGate.necessary", "DensityGate.full_envelope"},
    }
    result = {"lean_commit": LEAN, "mathlib_commit": MATHLIB, "modules": {}}
    with TemporaryDirectory() as work:
        env["LEAN_PATH"] = work + os.pathsep + env["LEAN_PATH"]
        for name, endpoints in modules.items():
            source = (HERE / (name + ".lean")).read_bytes()
            (Path(work) / (name + ".lean")).write_bytes(source)
            invocation = [tc / "bin/lean", *FLAGS, "--root=.", "-o", name+".olean", name+".lean"]
            log = subprocess.check_output(invocation, cwd=work, env=env, text=True)
            records = re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]", log)
            assert {qname for qname, _ in records} == endpoints
            axioms = sorted({ax.strip() for _, xs in records for ax in xs.split(",")})
            assert set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}
            replay = subprocess.check_output([tc / "bin/leanchecker", "-v", name], cwd=work,
                                             env=env, text=True, stderr=subprocess.STDOUT).strip()
            assert replay == "replaying " + name
            result["modules"][name] = {"source_sha256": sha256(source).hexdigest(),
                                      "endpoints": sorted(endpoints), "axioms": axioms, "replay": replay}
    return result


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--toolchain", required=True, type=Path)
    ap.add_argument("--mathlib", required=True, type=Path)
    opts = ap.parse_args()
    print(json.dumps(run(opts.toolchain.resolve(), opts.mathlib.resolve()), indent=2))
