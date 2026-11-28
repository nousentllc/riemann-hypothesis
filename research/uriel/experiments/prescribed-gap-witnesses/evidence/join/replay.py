"""Build the common-pair/field/slot bridge in one authenticated import environment."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FLAGS = ["--tstack=400000", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
         "-DmaxSynthPendingDepth=3", "-Dpp.unicode.fun=true", "-DmaxHeartbeats=4000000"]
IMPS = re.compile(r"^(?:public )?import\s+([\w.]+)", re.MULTILINE)
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"

def read(dir_name, filename):
    return json.loads((ROOT / dir_name / filename).read_text())

def replay(source, sdk, mathlib, caches):
    prior = read("slot", "prior_sources.json")
    fields = read("fields", "imports.json")
    pins = {n: [(p["git_blob"], p["cached_sha256"])] for n, p in fields.items()}
    for n, p in read("slot", "imports.json").items():
        pins.setdefault(n, []).append((p["blob"], p["olean"]))
    packages = {"fields": ["FieldEndpoints", "CoherentFields", "SynchronizedSlots", "SuccessiveFields", "PhysicalGap"],
                "pairs": ["PairSharing"], "slot": ["SlotGap"], "roster": ["FixedRoster"], "join": ["PrincipalBridge"]}
    modules = {name: ROOT / d / (name + ".lean") for d, ns in packages.items() for name in ns}
    rev = subprocess.check_output(["git", "-C", mathlib, "rev-parse", "HEAD"], text=True).strip()
    if rev != MATHLIB:
        raise ValueError("Mathlib revision differs")
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        libs = [work, mathlib / ".lake/build/lib/lean", *sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean")), sdk / "lib/lean"]
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, libs)), LEAN_SYSROOT=str(sdk), PATH=str(sdk / "bin") + os.pathsep + os.environ["PATH"])
        def run(*cmd):
            result = subprocess.run([sdk / "bin" / cmd[0], *cmd[1:]], cwd=work, env=env,
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if result.returncode or "declaration uses 'sorry'" in result.stdout:
                raise RuntimeError(result.stdout)
            return result.stdout.strip()
        version = run("lean", "--version")
        if not version.startswith("Lean (version 4.33.1,"):
            raise ValueError(version)
        visited, fresh, checks = set(), [], {}
        def build(n):
            if n in visited:
                return
            rel = Path(*n.split(".")).with_suffix(".lean")
            obj = (work / rel).with_suffix(".olean")
            if n in modules:
                data = modules[n].read_bytes()
            elif n in pins:
                data = prior[n].encode() if n in prior else (source / "src" / rel).read_bytes()
                oid = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
                if any(oid != p[0] for p in pins[n]):
                    raise ValueError("Source differs: " + n)
            else:
                if (source / "src" / rel).exists():
                    raise ValueError("Unpinned project dependency: " + n)
                return
            for dep in IMPS.findall(data.decode()):
                build(dep)
            obj.parent.mkdir(parents=True, exist_ok=True)
            if n not in modules:
                for root in caches:
                    cached = (root / rel).with_suffix(".olean")
                    if cached.is_file() and hashlib.sha256(cached.read_bytes()).hexdigest() in {v[1] for v in pins[n]}:
                        obj.symlink_to(cached)
                        visited.add(n)
                        return
                fresh.append(n)
            (work / rel).write_bytes(data)
            flags = [] if n in modules or n in prior else FLAGS
            out = run("lean", *flags, "--root=.", "-o", str(rel.with_suffix(".olean")), str(rel))
            if n in modules:
                ax = [s for s in out.splitlines() if "depends on axioms:" in s]
                if not ax or any("sorryAx" in s or not s.endswith("[propext, Classical.choice, Quot.sound]") for s in ax):
                    raise ValueError(out)
                kernel = run("leanchecker", "-v", n)
                if kernel != "replaying " + n:
                    raise ValueError(kernel)
                checks[n] = dict(sha256=hashlib.sha256(data).hexdigest(), kernel=kernel, axiom_count=len(ax))
                if n == "PrincipalBridge":
                    checks[n]["axioms"] = ax
            visited.add(n)
        build("PrincipalBridge")
        if set(modules) - visited:
            raise ValueError("Unreached bridge modules")
        return dict(version=version, mathlib=rev, original_modules=len(visited - set(modules) - set(prior)),
                    prior_modules=len(set(prior) & visited), rebuilt_inputs=fresh, supplements=checks)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("source", "toolchain", "mathlib"):
        parser.add_argument("--" + key, type=Path, required=True)
    parser.add_argument("--objects", type=Path, action="append", default=[])
    args = parser.parse_args()
    print(json.dumps(replay(args.source.resolve(), args.toolchain.resolve(), args.mathlib.resolve(),
                            [root.resolve() for root in args.objects]), indent=2))
