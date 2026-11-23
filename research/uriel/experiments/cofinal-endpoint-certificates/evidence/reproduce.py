"""Replay the endpoint study from an expanded research package. Python 3.10+."""
import argparse
from hashlib import sha1, sha256
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

EVIDENCE = Path(__file__).resolve().parent
PACKAGE = EVIDENCE.parent
SOURCE_PIN = "40e56bab026552e089d7afcfeff08d2defb9c005"
FINITE = (
    ("transport/checks.py", "transport/controls.json"),
    ("collar/collars.py", "collar/geometry.json"),
    ("outer/gaps.py", "outer/results.json"),
    ("regularity/probe.py", "regularity/results.json"),
    ("numeric/mesh.py", "numeric/results.json"),
    ("numeric/ceilings.py", "numeric/ceilings.json"),
)


def read_json(path):
    return json.loads(path.read_bytes())


def verify_manifest():
    manifest = PACKAGE / "SHA256SUMS"
    seen = set()
    for line in manifest.read_text(encoding="utf-8").splitlines():
        match = re.fullmatch(r"([a-fA-F0-9]{64}) [ *](.+)", line)
        if match is None:
            raise ValueError("invalid SHA256SUMS entry: " + line)
        expected, name = match.groups()
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError("unsafe manifest path: " + name)
        path = (PACKAGE / relative).resolve()
        if not path.is_relative_to(PACKAGE) or path == manifest or path in seen:
            raise ValueError("invalid or duplicate manifest path: " + name)
        if sha256(path.read_bytes()).hexdigest() != expected.lower():
            raise ValueError("SHA-256 mismatch: " + name)
        seen.add(path)
    inputs = [p for p in EVIDENCE.rglob("*") if p.suffix in {".py", ".lean", ".json"}]
    for path in inputs:
        if path.resolve() not in seen:
            raise ValueError("evidence missing from SHA256SUMS: " + str(path))
    upstream = {"bands.py": "ef10c85f30201af1d31d5609aaf07823a6c31ba2",
                "prime_mass.py": "b275109b8cdb40f0f38c1f8148a13e02015d17a7",
                "chi4_closed.py": "6f75b7570d0d69bb8030700cf779fffdbea9d7fc"}
    for name, blob in upstream.items():
        if digest_blob((EVIDENCE / "numeric" / name).read_bytes()) != blob:
            raise ValueError("numerical dependency differs from study 5396aa19: " + name)
    return len(seen)


def execute(script, args=()):
    run = subprocess.run([sys.executable, "-B", str(EVIDENCE / script), *map(str, args)],
                         cwd=EVIDENCE, stdout=subprocess.PIPE, text=True, check=True)
    return json.loads(run.stdout)


def compare(script, receipt, args=()):
    if execute(script, args) != read_json(EVIDENCE / receipt):
        raise ValueError(f"{script} differs from {receipt}")
    return receipt


def digest_blob(data):
    return sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def audit_source(source, git=None):
    if git is None and (source / ".git").exists():
        git = source
    source_args = ["--source", source]
    audit_args = source_args.copy()
    if git is not None:
        audit_args.extend(["--git", git])
    compare("transport/audit.py", "transport/source_check.json", audit_args)
    compare("transport/materialize_width.py", "transport/generated_width.json", source_args)
    fields = read_json(EVIDENCE / "collar/source_trace.json")
    imports = read_json(EVIDENCE / "collar/imports.json")
    if fields["commit"] != SOURCE_PIN or imports["pinned_source"] != SOURCE_PIN:
        raise ValueError("unexpected original source pin")
    expected = {"src/" + name.replace(".", "/") + ".lean": row["git_blob"]
                for name, row in imports["modules"].items()}
    line_count = 0
    for entry in fields["files"]:
        rel = entry["path"]
        if (rel in expected) != entry["in_kernel_import_closure"]:
            raise ValueError("field import scope differs: " + rel)
        if expected.setdefault(rel, entry["git_blob"]) != entry["git_blob"]:
            raise ValueError("field trace and import manifest disagree: " + rel)
        lines = (source / rel).read_text(encoding="utf-8").splitlines()
        for dec in entry["declarations"]:
            number = dec["line"]
            if not (1 <= number <= len(lines)) or not lines[number-1].strip().startswith(dec["text"]):
                raise ValueError(f"declaration prefix differs: {rel}:{number}")
            line_count += 1
    transport = read_json(EVIDENCE / "transport/inputs.json")
    for rel, blob in transport["source_blobs"].items():
        if expected.setdefault("src/" + rel, blob) != blob:
            raise ValueError("original import manifests disagree: " + rel)
    level = read_json(EVIDENCE / "level/imports.json")
    if level["pinned_source"] != SOURCE_PIN:
        raise ValueError("unexpected level source pin")
    for name, row in level["modules"].items():
        rel = "src/" + name.replace(".", "/") + ".lean"
        if expected.setdefault(rel, row["git_blob"]) != row["git_blob"]:
            raise ValueError("level import manifests disagree: " + rel)
    extension = read_json(EVIDENCE / "transport/extension/input_pins.json")
    for name, row in extension.items():
        rel = "src/" + name.replace(".", "/") + ".lean"
        if expected.setdefault(rel, row["source_blob"]) != row["source_blob"]:
            raise ValueError("host extension import manifests disagree: " + rel)
    for rel, checksum in transport["sources"].items():
        if sha256((source / "src" / rel).read_bytes()).hexdigest() != checksum:
            raise ValueError("transport intermediate source differs: " + rel)
    for rel, blob in expected.items():
        if digest_blob((source / rel).read_bytes()) != blob:
            raise ValueError("original source differs: " + rel)
    if git is not None:
        # One tree listing checks all hashes against the pinned commit, including trace-only files.
        ls = subprocess.check_output(["git", "-C", str(git), "ls-tree", "-r", "-z", SOURCE_PIN, "--", "src"])
        tree = {}
        for row in ls.split(b"\0"):
            if row:
                fields_raw, path_raw = row.split(b"\t", 1)
                tree[path_raw.decode()] = fields_raw.split()[2].decode()
        for rel, blob in expected.items():
            if tree.get(rel) != blob:
                raise ValueError("Git tree differs: " + rel)
    return dict(pin=SOURCE_PIN, transport=read_json(EVIDENCE / "transport/source_check.json"),
                generated_wrapper="authenticated source transformation; no elaboration",
                collar_trace_files=len(fields["files"]), collar_declaration_prefixes=line_count,
                collar_imports=len(imports["modules"]), transport_imports=len(transport["source_blobs"]),
                level_imports=len(level["modules"]), host_extension_imports=len(extension),
                transport_intermediates=len(transport["sources"]),
                checked_against_local_git_tree=(git is not None))


def check_lean(group, args):
    data = execute(group + "/replay.py", args)
    reference = read_json(EVIDENCE / group / "kernel.json")
    receipt_type = {"outer": "regularity", "level": "collar"}.get(group, group)
    keys = {
        "transport": ("mathlib_commit", "tracked_original_objects", "source_sha256", "axioms", "kernel"),
        "transport/extension": ("mathlib_commit", "pinned_sources", "module_sha256", "axioms", "kernel"),
        "collar": ("source_commit", "authenticated_original_sources", "mathlib",
                   "supplement_sha256", "declarations", "axioms", "kernel"),
        "regularity": ("mathlib", "source_sha256", "axioms", "replay"),
    }[receipt_type]
    for key in keys:
        if data[key] != reference[key]:
            raise ValueError(f"{group} kernel evidence differs on {key}")
    version_key = "version" if group.startswith("transport") else "lean"
    # Lean embeds the OS/architecture in the version string. Compare release and revision.
    rev = re.compile(r"^Lean \(version (\S+), .*?commit ([0-9a-f]{40}),")
    actual, recorded = rev.search(data[version_key]), rev.search(reference[version_key])
    if not actual or not recorded or actual.groups() != recorded.groups():
        raise ValueError(group + " Lean release or commit differs")
    if receipt_type == "collar":
        fresh = data["freshly_compiled_originals"]
        if len(set(fresh)) != len(fresh) or len(fresh) + data["reused_originals"] != data["authenticated_original_sources"]:
            raise ValueError(group + " build counts do not reconcile")
    return data


def main():
    if not __debug__:
        raise RuntimeError("Python assertions must be enabled for the experiment controls")
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source", type=Path, help="pinned original repository or extracted tree containing src/")
    ap.add_argument("--git", type=Path, help="optional separate Git repository with the original pinned tree")
    ap.add_argument("--toolchain", type=Path, help="Lean SDK root with bin/lean and bin/leanchecker")
    ap.add_argument("--mathlib", type=Path, help="pinned compiled Mathlib checkout")
    ap.add_argument("--objects", type=Path, action="append", default=[],
                    help="optional original project cache; repeat for further host extension caches")
    ap.add_argument("--work", type=Path, help="optional existing temporary-directory parent for the collar replay")
    ap.add_argument("--workers", type=int, default=3, help="worker limit for the collar replay")
    args = ap.parse_args()
    if args.git and not args.source:
        ap.error("--git requires --source")
    if bool(args.toolchain) != bool(args.mathlib) or (args.toolchain and not args.source):
        ap.error("the Lean replays require --toolchain, --mathlib and --source together")
    if not args.toolchain and (args.objects or args.work):
        ap.error("--objects and --work apply to the optional Lean replays")
    if args.workers < 1:
        ap.error("--workers must be positive")
    output = {"sha256_files_verified": verify_manifest()}
    output["finite_receipts_reproduced"] = [compare(script, receipt) for script, receipt in FINITE]
    if args.source:
        output["source"] = audit_source(args.source.resolve(), args.git.resolve() if args.git else None)
    if args.toolchain:
        common = ["--toolchain", args.toolchain.resolve(), "--mathlib", args.mathlib.resolve()]
        project = [*common, "--source", args.source.resolve()]
        extension_args = project.copy()
        for root in args.objects:
            extension_args.extend(["--objects", root.resolve()])
        if args.objects:
            project.extend(["--objects", args.objects[0].resolve()])
        output["kernel"] = {"regularity": check_lean("regularity", common),
                            "outer": check_lean("outer", common),
                            "transport": check_lean("transport", project)}
        with tempfile.TemporaryDirectory(dir=args.work, prefix="uriel-field-") as work:
            output["kernel"]["collar"] = check_lean("collar", [*project, "--work", work,
                                                              "--workers", args.workers])
            output["kernel"]["field_originals"] = compare("collar/check_imports.py",
                "collar/original_replay.json", [*common, "--work", work])
        with tempfile.TemporaryDirectory(dir=args.work, prefix="uriel-level-") as work:
            output["kernel"]["level"] = check_lean("level", [*project, "--work", work,
                                                             "--workers", args.workers])
        output["kernel"]["host_extension"] = check_lean("transport/extension", extension_args)
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
