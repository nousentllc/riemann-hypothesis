#!/usr/bin/env python3
"""Replay the fixed-seven experiment and compare the results with the packaged evidence.

The default needs Python 3.9+ and its standard library. It runs all finite panels,
including the conductor-2401 resultant. Run this file from any working directory.
Source, Git, PARI, kernel and package-integrity checks are optional.
"""
import argparse
from hashlib import sha1, sha256
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
PANELS = [
    ("base/check.py", "base/results.json"),
    ("base/carries.py", "base/carries.json"),
    ("ascent/control.py", "ascent/results.json"),
    ("descent/controls.py", "descent/controls.json"),
    ("ranks/geometry.py", "ranks/results.json"),
    ("moving/control.py", "moving/results.json"),
]


def read(name):
    return json.loads((HERE / name).read_text(encoding="utf-8"))


def equal(actual, expected, label):
    # Serializing also distinguishes a JSON boolean from the integers zero and one.
    def canonical(value):
        return json.dumps(value, sort_keys=True, allow_nan=False)
    if canonical(actual) != canonical(expected):
        raise ValueError("Evidence mismatch in " + label)


def manifest_check(manifest):
    manifest = manifest.resolve(strict=True)
    root = manifest.parent
    seen = set()
    for line in manifest.read_text(encoding="utf-8").splitlines():
        match = re.fullmatch(r"([a-f0-9]{64}) [ *](.+)", line)
        if not match:
            raise ValueError("Malformed SHA256SUMS line: " + line)
        digest, name = match.groups()
        path = (root / name).resolve(strict=True)
        if Path(name).is_absolute() or root not in path.parents or path in seen:
            raise ValueError("Out-of-tree or duplicate package entry: " + name)
        if sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError("Package checksum differs: " + name)
        seen.add(path)
    if not seen:
        raise ValueError("Empty package checksum manifest")
    return len(seen)


def checked_version(version):
    # The host triple can differ. Require identical Lean version and core revision.
    release = re.search(r"\bversion ([0-9.]+),", version)
    commit = re.search(r"\bcommit ([0-9a-f]{40})", version)
    if not release or not commit:
        raise ValueError("Unrecognized Lean version: " + version)
    return release.group(1), commit.group(1)


def kernel_semantics(receipt):
    receipt = dict(receipt)
    counts = receipt.pop("inputs")
    if set(counts) != {"new", "cached", "rebuilt"} or any(type(n) is not int or n < 0 for n in counts.values()):
        raise ValueError("Malformed kernel input accounting")
    equal(counts["new"], receipt["new_sources"], "new module count")
    equal(counts["cached"] + counts["rebuilt"],
          receipt["original_sources"] + receipt["prior_sources"], "input module count")
    receipt["version"] = checked_version(receipt["version"])
    return receipt



def ascent_anchors(source, repository, mathlib):
    # Unlike the complete import graph, the reading map cites a few historical
    # declarations that were compared but do not occur in the final Lean imports.
    counts = {}
    for row in read("ascent/source_map.json"):
        path = Path(row["path"])
        family = path.parts[0]
        checkout = mathlib if family == "Mathlib" else repository
        target = row["commit"] + ":" + path.as_posix()
        recorded = subprocess.check_output(["git", "-C", checkout, "rev-parse", target], text=True).strip()
        equal(recorded, row["blob"], target + " Git tree")
        if family == "research":
            data = subprocess.check_output(["git", "-C", checkout, "cat-file", "blob", target])
        else:
            source_copy = mathlib if family == "Mathlib" else source
            data = (source_copy / path).read_bytes()
        git_blob = sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        equal(git_blob, row["blob"], target)
        lines = data.decode().splitlines()
        for phrase, number in row["anchors"].items():
            if number < 1 or number > len(lines) or phrase not in lines[number - 1]:
                raise ValueError(f"Missing ascent anchor at {path}:{number}")
        counts[family] = counts.get(family, 0) + len(row["anchors"])
    return counts


def run(opts, temp):
    def command(name, *args):
        result = subprocess.run([sys.executable, "-I", str(HERE / name), *map(str, args)],
                                cwd=temp, text=True, capture_output=True)
        if result.returncode:
            raise ValueError(f"{name} exited {result.returncode}\n{result.stderr}\n{result.stdout}")
        return result.stdout

    def data(name, *args):
        return json.loads(command(name, *args))

    receipts = []
    def compare(value, filename):
        equal(value, read(filename), filename)
        receipts.append(filename)

    summary = {}
    if opts.sha256:
        summary["package_checksums"] = manifest_check(opts.sha256)
    for script, receipt in PANELS:
        compare(data(script), receipt)

    primary = data("numerics/relative.py")
    compare(primary, "numerics/results.json")
    extended = data("numerics/relative.py", "--extended")
    compare(extended, "numerics/extended.json")
    equal(dict(extended, rows=extended["rows"][:-1]), primary, "common resultant panel")
    equal(extended["rows"][-1]["conductor"], 2401, "extension conductor")
    summary["resultant_conductors"] = [r["conductor"] for r in extended["rows"]]

    derivation = command("ranks/derive.py").strip()
    equal(derivation, "Verified the derivation of LeastSupply.lean from the pinned previous supply.",
          "least-supply source reconstruction")
    summary["least_supply_derivation"] = True

    if opts.pari:
        executable = shutil.which(opts.pari)
        if not executable:
            raise ValueError(f"PARI/GP executable unavailable: {opts.pari}")
        # The version is recorded separately so different compatible builds can replay the arithmetic.
        gp_args = ["--gp", Path(executable).resolve(), "--timeout", opts.pari_timeout]
        actual = data("base/pari_check.py", *gp_args)
        expected = read("base/pari.json")
        versions = {tuple(row["pari_version"]) for row in actual}
        if len(versions) != 1:
            raise ValueError("Inconsistent PARI version across rows")
        summary["pari_version"] = list(versions.pop())
        def arithmetic(rows):
            return [{k: v for k, v in row.items() if k != "pari_version"} for row in rows]
        equal(arithmetic(actual), arithmetic(expected), "base/pari.json")
        receipts.append("base/pari.json")

        norms = data("numerics/independent_norm.py", *gp_args)
        frozen_norms = read("numerics/pari_norms.json")
        equal(norms["pari"], summary["pari_version"], "independent PARI version")
        # Arithmetic, generator, row order and digit counts remain exact fields.
        equal(dict(norms, pari=frozen_norms["pari"]), frozen_norms, "numerics/pari_norms.json")
        receipts.append("numerics/pari_norms.json")

    if opts.mathlib:
        compare(data("base/audit.py", "--mathlib", opts.mathlib), "base/audit.json")
    source_args = ["--source", opts.source]
    if opts.git:
        source_args.extend(["--git", opts.git])
    if opts.source:
        audit = data("replay.py", *source_args, "--audit-only")
        kernel_receipt = read("kernel.json")
        expected = {k: kernel_receipt[k] for k in
                    ("original_commit", "original_sources", "prior_sources", "new_sources")}
        equal(audit, dict(expected, git_verified=bool(opts.git)), "source audit")
        frozen_audit = read("audit.json")
        equal(frozen_audit, dict(expected, git_verified=True), "audit and kernel source counts")
        if opts.git:
            compare(audit, "audit.json")
        summary["source_audit"] = audit
        if opts.git:
            # Materialize the two preceding-experiment witnesses from the included
            # source corpus. The tracer verifies each against its commit's Git tree.
            previous = Path(temp) / "previous"
            pins = read("prior_pins.json")
            sources = read("prior_sources.json")
            for name in ("PhysicalGap", "PrincipalBridge"):
                rel = Path(pins[name]["path"]).relative_to("research/uriel/experiments/prescribed-gap-witnesses")
                target = previous / rel
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(sources[name].encode())
            compare(data("descent/trace.py", *source_args, "--previous", previous), "descent/trace.json")
            if opts.mathlib:
                summary["ascent_source_anchors"] = ascent_anchors(opts.source, opts.git, opts.mathlib)

    if opts.kernel:
        args = [*source_args, "--mathlib", opts.mathlib, "--toolchain", opts.toolchain,
                "--workers", opts.workers]
        for path in opts.objects:
            args.extend(["--objects", path])
        result = data("replay.py", *args)
        equal(kernel_semantics(result), kernel_semantics(read("kernel.json")), "kernel.json")
        receipts.append("kernel.json")
        summary["kernel"] = {"declarations": result["declarations"], "inputs": result["inputs"],
                             "version": result["version"]}
    summary["matched_json_receipts"] = receipts
    return summary


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    local = lambda value: Path(value).expanduser().resolve()
    ap.add_argument("--pari", nargs="?", const="gp", metavar="GP", help="replay PARI arithmetic (default executable: gp)")
    ap.add_argument("--pari-timeout", type=int, default=300, metavar="SEC",
                    help="time limit for each optional PARI group or resultant panel (default 300 seconds)")
    ap.add_argument("--source", type=local, metavar="DIR", help="authenticate the pinned original checkout containing src/")
    ap.add_argument("--git", type=local, metavar="DIR", help="also resolve original and prior commits in this Git repository (requires --source)")
    ap.add_argument("--mathlib", type=local, metavar="DIR", help="authenticate the pinned Mathlib checkout and base source anchors")
    ap.add_argument("--kernel", action="store_true", help="rebuild supplements, check axioms and run leanchecker; needs --source, --mathlib, --toolchain")
    ap.add_argument("--toolchain", type=local, metavar="DIR", help="pinned Lean SDK containing bin/lean and bin/leanchecker")
    ap.add_argument("--objects", action="append", type=local, default=[], metavar="DIR", help="kernel input object root; repeat this option for multiple roots; each reused object is hashed")
    ap.add_argument("--workers", type=int, default=3, metavar="N", help="parallel workers for the kernel replay (default 3)")
    ap.add_argument("--sha256", nargs="?", type=local, const=HERE.parent / "SHA256SUMS", metavar="MANIFEST",
                    help="verify every listed file in the package manifest (default ../SHA256SUMS beside evidence/)")
    opts = ap.parse_args()
    if opts.pari_timeout < 1 or (opts.pari_timeout != 300 and not opts.pari):
        ap.error("--pari-timeout must be positive and applies only to --pari")
    if opts.workers < 1:
        ap.error("--workers must be positive")
    if opts.git and not opts.source:
        ap.error("--git requires --source")
    if opts.kernel and not (opts.source and opts.toolchain and opts.mathlib):
        ap.error("--kernel requires --source, --toolchain and --mathlib")
    if (opts.objects or opts.toolchain or opts.workers != 3) and not opts.kernel:
        ap.error("--objects, --toolchain and --workers apply only to --kernel")
    try:
        with tempfile.TemporaryDirectory(prefix="seven-evidence-replay-") as temp:
            report = run(opts, temp)
    except (ValueError, OSError) as error:
        ap.exit(1, f"reproduce: {error}\n")
    print(json.dumps(report, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
