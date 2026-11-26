"""Replay the original and compact audits against the pinned Lean libraries."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
COMPACT_TARGET = "Lib.General.NumberTheory.QuadFieldSplitting"
LEAN_AND_MATHLIB = {
    "original": ("819816b2e0a3bf405af45ae5c7af2491d8f5bee6",
                 "0df444a360eaa60ab8c11dca51a86af692955474"),
    "compact": ("eb6cafb7290e8bd5f2937522d8d804f58f02bafc",
                "56a005855ea17e0b0958f73ec801ae140b0a1679"),
}
COMPACT_FLAGS = [
    "--tstack=400000", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
    "-DmaxSynthPendingDepth=3", "-Dpp.unicode.fun=true", "-DmaxHeartbeats=4000000",
]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(args, cwd=None, env=None):
    ran = subprocess.run([str(part) for part in args], cwd=cwd, env=env,
                         text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    result = ran.stdout.strip()
    if ran.returncode or "sorryAx" in result or "declaration uses `sorry`" in result:
        raise RuntimeError(f"failed: {args}\n{result[-6000:]}")
    return result


def check_pins(mode, source, mathlib, sdk):
    trace = json.loads((HERE / "source_trace.json").read_text())[mode]
    for file in trace["files"]:
        if sha256(source / file["path"]) != file["sha256"]:
            raise ValueError(f"source hash differs: {file['path']}")
    if mode == "compact":
        repo = source.parent.parent
        if command(["git", "rev-parse", "HEAD"], cwd=repo) != trace["commit"]:
            raise ValueError("unexpected compact checkout")
        if command(["git", "status", "--porcelain", "--", "grh-compact/src"], cwd=repo):
            raise ValueError("compact source tree is modified")
    lean_sha, mathlib_sha = LEAN_AND_MATHLIB[mode]
    compiler = command([sdk / "bin/lean", "--version"])
    checked_mathlib = command(["git", "rev-parse", "HEAD"], cwd=mathlib)
    if lean_sha not in compiler or checked_mathlib != mathlib_sha:
        raise ValueError("unexpected Lean or Mathlib revision")
    return trace["commit"], compiler, checked_mathlib


def search_path(sdk, paths):
    return dict(os.environ, LEAN_SYSROOT=str(sdk),
                LEAN_PATH=os.pathsep.join(str(path) for path in paths))


def module_path(root, name, suffix):
    return root.joinpath(*name.split(".")).with_suffix(suffix)


def compact_closure(source):
    visited = set()
    order = []

    def visit(module):
        path = module_path(source, module, ".lean")
        if module in visited or not path.is_file():
            return
        visited.add(module)
        for line in path.read_text().splitlines():
            found = re.match(r"^(?:(?:public|meta|private) )?import\s+(\S+)", line)
            if found:
                visit(found[1])
        order.append(module)

    visit(COMPACT_TARGET)
    return order


def replay_module(name, work, sdk, libs):
    filename = name + ".lean"
    shutil.copyfile(HERE / filename, work / filename)
    env = search_path(sdk, [work, *libs])
    olean = name + ".olean"
    elaboration = command([sdk / "bin/lean", "-j1", "-o", olean, filename], cwd=work, env=env)
    kernel = command([sdk / "bin/leanchecker", "-v", name], cwd=work, env=env)
    print(f"replayed {name}", flush=True)
    return {"module": name, "source_sha256": sha256(HERE / filename),
            "object_sha256": sha256(work / olean), "elaboration": elaboration, "kernel": kernel}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=LEAN_AND_MATHLIB)
    for option in ("source", "mathlib", "sdk", "receipt"):
        parser.add_argument("--" + option, required=True, type=Path)
    parser.add_argument("--objects", type=Path,
                        help="original compiled modules, or prepared compact order closure")
    args = parser.parse_args()
    source, mathlib, sdk = (getattr(args, name).resolve() for name in ("source", "mathlib", "sdk"))
    pin, compiler, mathlib_sha = check_pins(args.mode, source, mathlib, sdk)
    libraries = [mathlib / ".lake/build/lib/lean",
                 *sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean"))]
    # Some builds store the sibling packages beside Mathlib in the parent project.
    if mathlib.parent.name == "packages":
        libraries += sorted(mathlib.parent.glob("*/.lake/build/lib/lean"))
    with tempfile.TemporaryDirectory(prefix="frobenius-spacing-") as directory:
        work = Path(directory)
        native = []
        if args.mode == "original":
            if args.objects is None:
                parser.error("original mode requires the prepared original objects")
            libraries.insert(0, args.objects.resolve())
            names = ["OriginalSpacing", "OrbitControls"]
        else:
            objects = args.objects.resolve() if args.objects else work / "compact"
            libraries.insert(0, objects)
            env = search_path(sdk, libraries)
            for module in compact_closure(source):
                inp = module_path(source, module, ".lean")
                out = module_path(objects, module, ".olean")
                if args.objects is None:
                    out.parent.mkdir(parents=True, exist_ok=True)
                    command([sdk / "bin/lean", "-j1", *COMPACT_FLAGS, "-o", out, inp],
                            cwd=source, env=env)
                native.append({"module": module, "source_sha256": sha256(inp),
                               "object_sha256": sha256(out)})
            native[-1]["kernel"] = command([sdk / "bin/leanchecker", "-v", COMPACT_TARGET],
                                             cwd=source, env=env)
            names = ["SpacingLogic", "CompactOrder"]
        modules = [replay_module(name, work, sdk, libraries) for name in names]
    receipt = {"mode": args.mode, "source_pin": pin, "lean": compiler, "mathlib": mathlib_sha,
               "native_compact_order_imports": native, "audit_modules": modules}
    args.receipt.write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    main()
