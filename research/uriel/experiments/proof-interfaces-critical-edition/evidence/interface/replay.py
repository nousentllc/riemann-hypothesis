"""Check the local comparison lemmas against the frozen Lean 4.33.1 study environment."""

from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse
import json
import os
import re
import shutil
import subprocess
import sys


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def check_queries(output):
    names = {"ramp_kernel", "ramp_re", "centered_contrast", "trace_real",
             "no_integral_trace_one", "four_exceeds_ceiling", "lower_value_passes_ceiling"}
    matches = re.findall(r"'NousInterface\.(\w+)' depends on axioms: \[([^\]]*)\]", output)
    if {name for name, _ in matches} != names:
        raise ValueError("Incomplete axiom query output")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for name, values in matches:
        if set(values.split(", ")) - allowed:
            raise ValueError("Unexpected axiom for " + name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sdk", type=Path, default=Path("/private/tmp/lean-4.33.1-darwin_aarch64"))
    parser.add_argument("--mathlib", type=Path, default=Path("/private/tmp/uriel-rh-mathlib4331"))
    parser.add_argument("--objects", type=Path, default=Path("/private/tmp/nous-uncapped/restored/obj"))
    parser.add_argument("--study", type=Path, default=Path("/private/tmp/nous-ramdilates/fresh"))
    parser.add_argument("--original", type=Path, default=Path("/private/tmp/uriel-joint-original/src"))
    args = parser.parse_args()
    sdk, mathlib = args.sdk.resolve(), args.mathlib.resolve()
    relative = Path("Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean")
    source = args.original / relative
    local = Path(__file__).resolve().with_name("InterfaceChecks.lean")
    source_hash = digest(source)
    if source_hash != "ca0ca8acb80ff4ffc36896204650f9ca16167193a22c36a140402b27cfc8c336":
        raise ValueError("Original CharFamily source differs from the audited copy")
    version = subprocess.check_output([sdk / "bin/lean", "--version"], text=True).strip()
    mathlib_commit = subprocess.check_output(
        ["git", "-C", mathlib, "rev-parse", "HEAD"], text=True
    ).strip()
    if "819816b2e0a3" not in version or mathlib_commit != "0df444a360eaa60ab8c11dca51a86af692955474":
        raise ValueError("Toolchain differs from the comparison environment")
    receipt = dict(compiler=version, mathlib=mathlib_commit, source_sha256=source_hash,
                   comparison_sha256=digest(local), ramfield_object_sha256=digest(args.study / "RamField.olean"),
                   commands=[])
    with TemporaryDirectory() as temp:
        work = Path(temp)
        (work / relative).parent.mkdir(parents=True)
        shutil.copyfile(source, work / relative)
        shutil.copyfile(local, work / local.name)
        paths = [work, args.study.resolve(), args.objects.resolve(), mathlib / ".lake/build/lib/lean",
                 *sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean")), sdk / "lib/lean"]
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, paths)), LEAN_SYSROOT=str(sdk))
        for path in (relative, Path(local.name)):
            module = ".".join(path.with_suffix("").parts)
            for command in (["lean", "-j1", "-o", str(path.with_suffix(".olean")), str(path)],
                            ["leanchecker", "-v", module]):
                result = subprocess.run([sdk / "bin" / command[0], *command[1:]], cwd=work,
                                        env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                if result.returncode:
                    sys.stderr.write(result.stdout)
                    raise SystemExit(result.returncode)
                if path == Path(local.name) and command[0] == "lean":
                    check_queries(result.stdout)
                receipt["commands"].append(dict(command=command, exit=result.returncode,
                                                output=result.stdout.strip()))
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
