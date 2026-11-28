"""Prepare pinned source, compile the analytic import closure and replay each module."""
import argparse
from collections import deque
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
PIN = "40e56bab026552e089d7afcfeff08d2defb9c005"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
LEAN = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
TARGET = "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow"
EXCERPTS = [
    ("src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Window1.lean",
     "UpperTheory.V.Win.window1", ""),
    ("src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MajAtAddRight.lean",
     "numeric", "GlobalTheory.CutNum"),
    ("src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsRanksRankValFrame.lean",
     "exists_even_between", "GlobalTheory.EX"),
]
FLAGS = ["-j1", "--tstack=400000", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
         "-DmaxSynthPendingDepth=3", "-Dpp.unicode.fun=true", "-DmaxHeartbeats=4000000"]


def dump(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True, allow_nan=False) + "\n")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])


def original(path):
    return git(ROOT, "show", f"{PIN}:{path}")


def prepare(work):
    tree = git(ROOT, "ls-tree", "-r", "-z", "--name-only", PIN, "src").decode().split("\0")
    project = {p[4:-5].replace("/", "."): p for p in tree if p.endswith(".lean")}
    sources, visiting = {}, set()

    def visit(module):
        if module in sources:
            return
        if module in visiting:
            raise ValueError(f"Cyclic import at {module}")
        visiting.add(module)
        path = project[module]
        data = original(path)
        imports = []
        for header in re.findall(r"(?m)^import[ \t]+([^\n]+)", data.decode()):
            imports.extend(header.split("--")[0].strip().split())
        for dependency in imports:
            if dependency in project:
                visit(dependency)
            elif dependency != "Mathlib" and not dependency.startswith(("Mathlib.", "Lean.", "Init.", "Std.")):
                raise ValueError(f"Unresolved import {dependency} in {module}")
        target = work / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        sources[module] = dict(module=module, path=path, sha256=sha(data), imports=imports)
        visiting.remove(module)

    visit(TARGET)
    fragments = ["import Mathlib\n"]
    spans = []
    for path, name, namespace in EXCERPTS:
        data = original(path)
        lines = data.decode().splitlines(keepends=True)
        first, = (i for i, line in enumerate(lines) if line.startswith(f"theorem {name} "))
        end = next((i for i in range(first+1, len(lines)) if lines[i].strip() and
                    not lines[i][0].isspace()), len(lines))
        while end > first and not lines[end-1].strip():
            end -= 1
        block = "".join(lines[first:end])
        if namespace:
            fragments.append("namespace " + namespace + "\n")
        fragments.append(block)
        if namespace:
            fragments.append("end " + namespace + "\n")
        spans.append(dict(path=path, start=first+1, end=end, source_sha256=sha(data),
                          declaration=name, wrapper_namespace=namespace, block_sha256=sha(block.encode())))
    joined = "\n".join(fragments).encode()
    (work/"src"/"UrielFragments.lean").write_bytes(joined)
    dump(work/"prepared.json", dict(pin=PIN, modules=list(sources.values()), excerpts=spans,
                                    fragments_sha256=sha(joined)))


def environment(tc, mathlib):
    env = dict(os.environ, PATH=str(tc/"bin") + os.pathsep + os.environ["PATH"], LEAN_SYSROOT=str(tc))
    cmd = lambda args: subprocess.check_output(args, env=env, cwd=mathlib, text=True).strip()
    version = cmd([str(tc/"bin"/"lean"), "--githash"])
    if version != LEAN:
        raise ValueError(f"Unexpected Lean commit {version}")
    checked = {}
    for pkg in json.loads(original("lake-manifest.json"))["packages"]:
        repo = mathlib if pkg["name"] == "mathlib" else mathlib/".lake"/"packages"/pkg["name"]
        actual = git(repo, "rev-parse", "HEAD").decode().strip()
        if actual != pkg["rev"] or git(repo, "status", "--porcelain", "--untracked-files=no").strip():
            raise ValueError(f"Unexpected package revision or tracked edits in {pkg['name']}")
        checked[pkg["name"]] = actual
    if checked.get("mathlib") != MATHLIB:
        raise ValueError("Mathlib pin differs from the registered protocol")
    env["LEAN_PATH"] = cmd([str(tc/"bin"/"lake"), "env", "printenv", "LEAN_PATH"])
    return env, dict(lean=version, version=cmd([str(tc/"bin"/"lean"), "--version"]),
                     packages=checked)


def compare_edges(terms,graph):
    """Join the first experiment's exact lexical edges to local proof-value paths."""
    previous = json.loads((HERE.parent/"initial/results/source_graph.json").read_text())
    result = []
    for e in previous["edges"]:
        path, src = e["source"].split("::")
        source, dest = "Deduction."+src, "Deduction."+e["reference"]
        if "/DedekindLFunctions/" not in path or source not in terms:
            continue
        queue = deque([[source]])
        visited = {source}
        witness = None
        while queue:
            chain = queue.popleft()
            if chain[-1] == dest:
                witness = chain
                break
            for n in graph.get(chain[-1], []):
                if n not in visited:
                    visited.add(n)
                    queue.append(chain+[n])
        result.append(dict(source=source, target=dest, proof_path=witness,
                           direct_value=dest in terms[source]["value"],direct_type=dest in terms[source]["type"]))
    return result


def execute(tc, mathlib, work, output, stage):
    source = json.loads((work/"prepared.json").read_text())
    # Authenticate prepared material again at execution; stale or substituted input stops the audit.
    for row in source["modules"]:
        data = (work/row["path"]).read_bytes()
        if data != original(row["path"]) or sha(data) != row["sha256"]:
            raise ValueError(row["path"])
    if sha((work/"src"/"UrielFragments.lean").read_bytes()) != source["fragments_sha256"]:
        raise ValueError("Changed excerpt wrapper")
    env, versions = environment(tc, mathlib)
    root = work/"src"
    build = work/"oleans"
    build.mkdir(exist_ok=True)
    env["LEAN_PATH"] = str(build) + os.pathsep + env["LEAN_PATH"]
    lean, checker = str(tc/"bin"/"lean"), str(tc/"bin"/"leanchecker")
    report_file = output/"lean_build.json"
    if stage == "build":
        if any(build.iterdir()):
            raise ValueError("Use a fresh --work directory for a source build")
        report = dict(**source, toolchain=versions, flags=FLAGS, operations=[],
                      full_main_built=False, imported_mathlib_replayed=False)
    else:
        compiled = json.loads(report_file.read_text())
        if compiled["toolchain"] != versions or compiled["pin"] != PIN or compiled["modules"] != source["modules"]:
            raise ValueError("Build environment changed")
        required = {("module_compile",r["module"]) for r in source["modules"]} | {("excerpt_compile","UrielFragments")}
        accepted = {(r["stage"],r["name"]) for r in compiled["operations"] if r["accepted_as_expected"]}
        if required - accepted:
            raise ValueError("Compile the original modules and excerpts before inspecting terms")
        report_file = output/"lean_audit.json"
        report = dict(pin=PIN, toolchain=versions, operations=[],
                      audit_source_sha256=sha((HERE/"Audit.lean").read_bytes()),
                      sharpness_source_sha256=sha((HERE/"Sharpness.lean").read_bytes()))
    def run(kind, name, args, expect_rejection=False):
        start = time.monotonic()
        proc = subprocess.run(args, env=env, cwd=root, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, text=True)
        text = proc.stdout.replace(str(work), "<work>").replace(str(tc), "<toolchain>").replace(str(mathlib), "<mathlib>")
        valid = proc.returncode == 0
        if expect_rejection:
            valid = proc.returncode != 0 and "type mismatch" in text.lower() and "False" in text
        elif kind.endswith("replay"):
            valid = valid and f"replaying {name}" in text
        if "declaration uses 'sorry'" in text:
            valid = False
        record = dict(stage=kind, name=name, exit=proc.returncode, accepted_as_expected=valid,
                      seconds=round(time.monotonic()-start, 3))
        if text.strip() and (kind != "audit_terms" or not valid):
            record["output"] = text.strip()
        report["operations"].append(record)
        dump(report_file, report)
        print(f"{kind} {name} => {proc.returncode}", flush=True)
        if not valid:
            raise RuntimeError(text[-5000:])
        return text

    if stage == "build":
        for mod in [row["module"] for row in source["modules"]] + ["UrielFragments"]:
            base = Path(*mod.split("."))
            olean = (build/base).with_suffix(".olean")
            olean.parent.mkdir(parents=True, exist_ok=True)
            run("excerpt_compile" if mod == "UrielFragments" else "module_compile", mod,
                [lean, *FLAGS, "--root=.", "-o", str(olean), str(base.with_suffix(".lean"))])
        for mod in [row["module"] for row in source["modules"]] + ["UrielFragments"]:
            run("excerpt_replay" if mod == "UrielFragments" else "module_replay", mod, [checker, "-v", mod])
    else:
        sharp = root/"UrielSharpness.lean"
        sharp.write_bytes((HERE/"Sharpness.lean").read_bytes())
        run("supplement_compile", "UrielSharpness", [lean, *FLAGS, "-o", str(build/"UrielSharpness.olean"), str(sharp)])
        run("supplement_replay", "UrielSharpness", [checker, "-v", "UrielSharpness"])
        control = root/"UrielControls.lean"
        control.write_text("import Mathlib\nnamespace UrielControl\n"
                           "theorem unused : True := True.intro\naxiom injected : False\n"
                           "theorem usesInjected : False := injected\nend UrielControl\n")
        run("control_compile", "UrielControls", [lean, *FLAGS, "-o", str(build/"UrielControls.olean"), str(control)])
        rejected = root/"UrielRejected.lean"
        rejected.write_text("import Mathlib\nexample : False := True.intro\n")
        run("reject_false", "True.intro : False", [lean, *FLAGS, str(rejected)], expect_rejection=True)
        audit = root/"UrielAudit.lean"
        audit.write_bytes((HERE/"Audit.lean").read_bytes())
        raw = run("audit_terms", "UrielAudit", [lean, *FLAGS, str(audit)])
        rows = [json.loads(line.removeprefix("URIEL_TERM ")) for line in raw.splitlines() if line.startswith("URIEL_TERM ")]
        dump(output/"lean_terms.json", rows)
        if not rows:
            raise ValueError("No elaborated declarations returned")
        terms = {row["name"]:row for row in rows}
        target = terms["Deduction.zeroFree_of_rpow_window"]
        if "Deduction.lemmaL" not in target["value"] or "UrielControl.unused" in target["value"]:
            raise ValueError("Direct dependency control failed")
        if terms["UrielControl.usesInjected"]["axioms"] != ["UrielControl.injected"]:
            raise ValueError("Injected axiom control failed")
        for row in rows:
            if not row["name"].startswith("UrielControl.") and set(row["axioms"]) - {"propext","Classical.choice","Quot.sound"}:
                raise ValueError(f"Unexpected axioms for {row['name']}")
        graph = [json.loads(line.removeprefix("URIEL_EDGE ")) for line in raw.splitlines() if line.startswith("URIEL_EDGE ")]
        adj = {r["name"]:r["value"] for r in graph}
        dump(output/"lean_edges.json", dict(analytic_value_graph=adj,prior_comparison=compare_edges(terms,adj)))
        (output/"axioms.txt").write_text("\n".join(line for line in raw.splitlines() if
                                      not line.startswith(("URIEL_TERM ","URIEL_EDGE ")))+"\n")


def finish(tc, mathlib, work, out):
    """Check all recorded stages, hash the checked objects and run a direct kernel control."""
    env, versions = environment(tc,mathlib)
    build = json.loads((out/"lean_build.json").read_text())
    audit = json.loads((out/"lean_audit.json").read_text())
    terms = json.loads((out/"lean_terms.json").read_text())
    edges = json.loads((out/"lean_edges.json").read_text())["prior_comparison"]
    if any(r["toolchain"] != versions or r["pin"] != PIN for r in (build,audit)):
        raise ValueError("Recorded versions differ")
    if audit["audit_source_sha256"] != sha((HERE/"Audit.lean").read_bytes()) or audit["sharpness_source_sha256"] != sha((HERE/"Sharpness.lean").read_bytes()):
        raise ValueError("The recorded term audit does not match the supplied source")
    ops = build["operations"] + audit["operations"]
    if any(not r["accepted_as_expected"] for r in ops):
        raise ValueError("An original proof or audit operation failed")
    originals = {r["module"] for r in build["modules"]}
    required = {"module_compile":originals,"module_replay":originals,
        "excerpt_compile":{"UrielFragments"},"excerpt_replay":{"UrielFragments"},
        "supplement_compile":{"UrielSharpness"},"supplement_replay":{"UrielSharpness"},
        "control_compile":{"UrielControls"},"reject_false":{"True.intro : False"},"audit_terms":{"UrielAudit"}}
    for kind, names in required.items():
        rows = [r for r in ops if r["stage"]==kind]
        if len(rows)!=len(names) or {r["name"] for r in rows}!=names:
            raise ValueError(f"Incomplete stage {kind}")
        if kind.endswith("replay") and any(r["output"].splitlines()!=["replaying "+r["name"]] for r in rows):
            raise ValueError(f"Unexpected replay coverage at {kind}")
    objects = {n:sha((work/"oleans"/Path(*n.split("."))).with_suffix(".olean").read_bytes())
               for n in sorted(originals|{"UrielFragments","UrielSharpness","UrielControls"})}
    proc = subprocess.run([str(tc/"bin"/"lean"),"-j1","KernelControl.lean"],env=env,cwd=HERE,
                          capture_output=True,text=True)
    controls = proc.stdout.strip().splitlines()
    if proc.returncode or controls != ["positive control accepted: True.intro at True",
                                      "negative control rejected: declTypeMismatch at False"]:
        raise ValueError(proc.stderr+proc.stdout)
    clean = [r for r in terms if not r["name"].startswith("UrielControl.")]
    std = {"propext","Classical.choice","Quot.sound"}
    if any(set(r["axioms"])-std for r in clean):
        raise ValueError("Unexpected proof assumptions")
    targets = {r["name"]:r for r in terms}
    if targets["UrielControl.usesInjected"]["axioms"]!=["UrielControl.injected"] or any(
            any(x.startswith("UrielControl.") for x in r["value"]+r["type"]+r["axioms"]) for r in clean):
        raise ValueError("Synthetic control leaked or was missed")
    source_count = sum(p.endswith(b".lean") for p in git(ROOT,"ls-tree","-r","-z","--name-only",PIN,"src").split(b"\0"))
    dump(out/"formal_summary.json", dict(pin=PIN,project_source_files=source_count,original_compiled=len(originals),
        original_kernel_replayed=len(originals),excerpt_declarations=len(build["excerpts"]),
        audited_original_analytic=sum(r["name"].startswith("Deduction.") for r in clean),
        direct_older_edges=sum(r["direct_value"] for r in edges),
        reachable_older_edges=sum(r["proof_path"] is not None for r in edges),compared_older_edges=len(edges),
        clean_axioms=sorted(set().union(*(set(r["axioms"]) for r in clean))),
        injected_axioms=targets["UrielControl.usesInjected"]["axioms"],kernel_control=controls,
        kernel_control_source_sha256=sha((HERE/"KernelControl.lean").read_bytes()),object_sha256=objects,
        imported_mathlib_replayed_from_empty=False,whole_Main_built=False))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("stage", choices=("prepare", "build", "audit", "finish"))
    p.add_argument("--work", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--toolchain", type=Path)
    p.add_argument("--mathlib", type=Path)
    a = p.parse_args()
    work = a.work.resolve()
    if a.stage == "prepare":
        prepare(work)
    else:
        if not a.toolchain or not a.mathlib:
            p.error("Provide --toolchain and --mathlib for formal execution")
        if a.stage == "finish":
            finish(a.toolchain.resolve(), a.mathlib.resolve(), work, a.out.resolve())
        else:
            execute(a.toolchain.resolve(), a.mathlib.resolve(), work, a.out.resolve(), a.stage)


if __name__ == "__main__":
    main()
