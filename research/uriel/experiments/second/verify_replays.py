"""Compare raw results after a second interpreter run and an unchanged first-round replay."""
import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
FILES = ("analytic.json","arithmetic.json","cohomology.json","slopes.json","prime_windows.json","finite_certificate.json")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verified_tests(path,manifest,exit_key):
    text = (path/"tests.txt").read_text()
    match = re.search(r"Ran (\d+) tests? in ",text)
    if manifest[exit_key]!=0 or not match or not text.rstrip().endswith("OK"):
        raise ValueError(f"Failed or missing tests in {path}")
    return int(match[1])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--other",required=True,type=Path)
    parser.add_argument("--first-round",required=True,type=Path)
    parser.add_argument("--out",required=True,type=Path)
    args = parser.parse_args()
    runs=[]
    for path in (HERE/"results",args.other):
        manifest=json.loads((path/"numerical_run.json").read_text())
        actual={n:digest(path/n) for n in FILES}
        if actual!=manifest["outputs"]:
            raise ValueError(f"Stale manifest in {path}")
        runs.append(dict(python=manifest["python"],mpmath=manifest["mpmath"],
                         tests=verified_tests(path,manifest,"test_exit"),sha256=actual))
    if runs[0]["sha256"]!=runs[1]["sha256"]:
        raise ValueError("Numerical artifacts differ across independent runs")
    replay = args.first_round
    manifest=json.loads((replay/"run.json").read_text())
    first = {n:digest(replay/n) for n in ("numerical.json","source_graph.json")}
    if any(digest(HERE.parent/"initial/results"/n)!=h for n,h in first.items()):
        raise ValueError("First-round replay differs from its stored scientific outputs")
    result=dict(second_round=runs, first_round=dict(python=manifest["python"],numpy=manifest["numpy"],
                scipy=manifest["scipy"],tests=verified_tests(replay,manifest,"test_exit_code"),sha256=first))
    args.out.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")


if __name__=="__main__":
    main()
