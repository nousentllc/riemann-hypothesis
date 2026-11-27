"""Reproduce the source counts and declaration anchors for the GRH comparison."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def git_revision(root):
    return subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True
    ).strip()


def lean_sources(root):
    return {
        path.relative_to(root).as_posix(): path.read_bytes()
        for path in sorted(root.rglob("*.lean"))
    }


def source_counts(files):
    lines = [line for raw in files.values() for line in raw.splitlines()]
    return {
        "files": len(files),
        "physical_lines_including_comments_and_blanks": len(lines),
        "nonblank_lines_including_comments": sum(bool(line.strip()) for line in lines),
    }


def compare_trees(first, second):
    common = first.keys() & second.keys()
    return {
        "equal_files": sum(first[name] == second[name] for name in common),
        "changed_files": sorted(name for name in common if first[name] != second[name]),
        "first_only": sorted(first.keys() - second.keys()),
        "second_only": sorted(second.keys() - first.keys()),
    }


def declaration_lines(files, specifications):
    result = {}
    for name, marker in specifications:
        lines = [
            number
            for number, line in enumerate(files[name].decode("utf-8").splitlines(), 1)
            if marker in line
        ]
        if len(lines) != 1:
            raise ValueError(f"Expected one anchor for {marker!r} in {name}, got {lines}")
        result[marker] = {"file": name, "line": lines[0]}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("release", type=Path)
    parser.add_argument("previous_readable", type=Path)
    args = parser.parse_args()
    release_sha = git_revision(args.release)
    previous_sha = git_revision(args.previous_readable)
    if release_sha != "72fead102f663d5c7a407964a13dc0cf9d977207":
        parser.error("release checkout must be at 72fead102f663d5c7a407964a13dc0cf9d977207")
    if previous_sha != "e063a923620ee7787b4a1270421478645bf66bdb":
        parser.error("previous readable checkout must be at e063a923620ee7787b4a1270421478645bf66bdb")
    readable = lean_sources(args.release / "grh" / "src")
    compact = lean_sources(args.release / "grh-compact" / "src")
    previous = lean_sources(args.previous_readable / "src")
    statements = readable["Statements.lean"]
    assert statements == compact["Statements.lean"]
    print(json.dumps({
        "release_commit": release_sha,
        "previous_readable_commit": previous_sha,
        "readable": source_counts(readable),
        "compact": source_counts(compact),
        "release_readable_versus_previous_readable": compare_trees(readable, previous),
        "shared_statements": {
            "byte_identical": True,
            "bytes": len(statements),
            "sha256": hashlib.sha256(statements).hexdigest(),
        },
        "compact_anchors": declaration_lines(compact, [
            ("New/Main.lean", "lemma star_inequality"),
            ("New/Main.lean", "lemma eventually_primeError_le_rpow"),
            ("New/Main.lean", "let D' := {D with logX₁ := u"),
            ("New/Main.lean", "lemma New.grh"),
            ("New/Data/DataExist.lean", "lemma exists_data P"),
            ("New/Data/AdmissibleData.lean", "def nominalWeight"),
            ("New/Data/Different.lean", "lemma Parameters.card_placeClass_eq"),
            ("New/Endgame/ShortAndEnough.lean", "lemma Data.remainder_eq"),
            ("New/Endgame/OneSidedCriterion.lean", "lemma IsPolar.exists_window_sub_mul_le"),
            ("Lib/PadicComparison/Primitive/TiltedTheory.lean", "def tiltTheory"),
        ]),
        "readable_anchors": declaration_lines(readable, [
            ("New/Reduction/MainInequality.lean", "theorem star_inequality"),
            ("New/Reduction/OneSidedBound.lean", "lemma eventually_abs_primeRemainder_exp_le"),
            ("New/Reduction/OneSidedBound.lean", "theorem eventually_primeRemainder_le_rpow"),
            ("Lib/PadicComparison/Primitive/PeriodCoefficients.lean", "def tiltTheory"),
        ]),
    }, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
