"""Replay the conductor-one slot extension on source-pinned project and research inputs."""
import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
FLAGS = ["--tstack=400000", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
         "-DmaxSynthPendingDepth=3", "-Dpp.unicode.fun=true", "-DmaxHeartbeats=4000000"]
IMPORT = re.compile(r"^(?:public )?import\s+([\w.]+)", re.MULTILINE)


def replay(source, sdk, mathlib, caches):
    pins = json.loads((HERE / "imports.json").read_text())
    priors = json.loads((HERE / "prior_sources.json").read_text())
    math_rev = subprocess.check_output(["git", "-C", mathlib, "rev-parse", "HEAD"], text=True).strip()
    if math_rev != MATHLIB:
        raise ValueError("Mathlib revision differs")
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        libraries = [work, mathlib / ".lake/build/lib/lean",
                     *sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean")), sdk / "lib/lean"]
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, libraries)), LEAN_SYSROOT=str(sdk),
                   PATH=str(sdk / "bin") + os.pathsep + os.environ["PATH"])

        def run(*args):
            result = subprocess.run([sdk / "bin" / args[0], *args[1:]], cwd=work, env=env,
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if result.returncode or "declaration uses 'sorry'" in result.stdout:
                raise RuntimeError(result.stdout)
            return result.stdout.strip()

        version = run("lean", "--version")
        if not version.startswith("Lean (version 4.33.1,"):
            raise ValueError(version)
        visited = set()
        rebuilt = []
        def prepare(name):
            if name in visited or name not in pins:
                return
            rel = Path(*name.split(".")).with_suffix(".lean")
            data = priors[name].encode() if name in priors else (source / "src" / rel).read_bytes()
            oid = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
            if oid != pins[name]["blob"]:
                raise ValueError("Source mismatch: " + name)
            for dep in IMPORT.findall(data.decode()):
                prepare(dep)
            target = (work / rel).with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            for root in caches:
                obj = (root / rel).with_suffix(".olean")
                if obj.is_file() and hashlib.sha256(obj.read_bytes()).hexdigest() == pins[name]["olean"]:
                    target.symlink_to(obj)
                    break
            else:
                (work / rel).write_bytes(data)
                run("lean", *([] if name in priors else FLAGS), "--root=.", "-o",
                    str(rel.with_suffix(".olean")), str(rel))
                rebuilt.append(name)
            visited.add(name)

        module = (HERE / "SlotGap.lean").read_bytes()
        for dep in IMPORT.findall(module.decode()):
            prepare(dep)
        if visited != set(pins):
            raise ValueError("Import closure changed")
        (work / "SlotGap.lean").write_bytes(module)
        output = run("lean", "--root=.", "-o", "SlotGap.olean", "SlotGap.lean")
        axioms = [line for line in output.splitlines() if "depends on axioms:" in line]
        expected = ["'GapFirst.Slot." + name + "' depends on axioms: [propext, Classical.choice, Quot.sound]"
                    for name in ("principalDirect", "allCentersOneLift", "zeroOnModel", "eraseThree", "principalGap")]
        if axioms != expected:
            raise ValueError(output)
        kernel = run("leanchecker", "-v", "SlotGap")
        if kernel != "replaying SlotGap":
            raise ValueError(kernel)
        return dict(version=version, mathlib=math_rev, original_sources=len(pins)-len(priors),
                    pinned_prior_sources=len(priors), rebuilt=rebuilt, axioms=axioms, kernel=kernel,
                    supplement_sha256=hashlib.sha256(module).hexdigest())

if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    for arg in ("source", "toolchain", "mathlib"):
        p.add_argument("--" + arg, type=Path, required=True)
    p.add_argument("--objects", type=Path, action="append", default=[])
    args = p.parse_args()
    print(json.dumps(replay(args.source.resolve(), args.toolchain.resolve(), args.mathlib.resolve(),
                            [d.resolve() for d in args.objects]), indent=2))
