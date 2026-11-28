"""Authenticate cited Git source spans and test selected witness-identity uses."""
import argparse
from collections import defaultdict
from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
import re
import sys

from build_original import HERE, PIN, dump, pinned_source, pinned_tree

sys.path.insert(0, str(HERE.parent / "initial"))
from source_audit import mask_comments

PREFIX = "https://github.com/nousentllc/riemann-hypothesis/blob/"
LINK = re.compile(r"\[([^\]\n]+)\]\((" + re.escape(PREFIX) + r"[^)\s]+)\)")
ANCHOR = re.compile(r"(?P<pin>[^/]+)/(?P<path>src/[^#?]+\.lean)"
                    r"(?:#L(?P<start>[0-9]+)(?:-L(?P<end>[0-9]+))?)?")
AA = "src/Development/AutomorphicArithmetic/"


@dataclass(frozen=True)
class Guard:
    role: str
    file: str
    line: int
    text: str
    before: str
    after: str


GUARDS = (
    Guard("two-primary exceptions for the selected ordered primes",
          "AutomorphicVarieties/LayeredIsomorphisms/ThmBabOf.lean", 76,
          "obtain ⟨ExcA, hcardA, hxA⟩ := hA e t hAdm X q d hqd hlog L₀ hTB hAB", "X q d", "X d q"),
    Guard("one selector for the two-primary and odd-prime union",
          "AutomorphicVarieties/LayeredIsomorphisms/ThmBabOf.lean", 88,
          "obtain ⟨Y, hY, hgood⟩ := window R (eps / (2 * CK)) Ct X (ExcA ∪ B'.biUnion g) heta hetaCt",
          "(ExcA ∪ B'.biUnion g)", "ExcA"),
    Guard("window theorem applied to the selected pair",
          "CharacterBoxes/WinPairs.lean", 35,
          "obtain ⟨W, hW0, hW2, hWV⟩ := hX0 X hXX0 q d hpg.pair", "q d", "d q"),
    Guard("common pair and page at the rescaled point in the returned data",
          "CharacterBoxes/WinPairs.lean", 65,
          "refine ⟨X ^ (1 / J), q, d, e x', ?_, ?_, ?_, ?_, ?_, ?_⟩", "e x'", "e (k*x')"),
    Guard("field identified by the same host and kernel data",
          "ShortNorms/supplyOfAdmOf.lean", 129,
          "· have hCF := UpperTheory.Top.isChiField ψ R.toFrame H.toHostRaw hker", "H.toHostRaw", "Hother.toHostRaw"),
    Guard("bound applied to that host field",
          "ShortNorms/supplyOfAdmOf.lean", 131,
          "have hv := hW.bound H.E hCF", "H.E", "Hother.E"),
    Guard("chain's selected TT equated to its actual indexed host",
          "PrimitiveCosets/LevelGmLeOnFamilyScales.lean", 17,
          "have hTT : TT = (Fm.D x i0).host.TT := by", "Fm.D x i0", "Fm.D x j"),
    Guard("CoreAtH uses one index for host and TT",
          "PrimitiveCosets/WindowInequalityOfArtinInputs.lean", 12,
          "∃ i : Fm.Ix x, CoreAtH (Fm.D x i).host.toHostRaw (Fm.D x i).host.TT eD eL K cHH eK eps x",
          "(Fm.D x i).host.TT", "(OtherFm.D x i).host.TT"),
    Guard("final application uses the same i for the host and its assumptions",
          "PrimitiveCosets/WindowInequalityOfArtinInputs.lean", 25,
          "exact hx1 x (le_of_max_le_left hx) _ ((core Fm).D x i).host.toHostAx _ (hE x (le_of_max_le_right b) i) hi",
          "(le_of_max_le_right b) i", "(le_of_max_le_right b) j"),
)


def doc_anchors():
    refs = defaultdict(set)
    for doc in sorted(HERE.glob("*.md")):
        content = doc.read_text(encoding="utf8")
        links = LINK.findall(content)
        bare = re.findall(re.escape(PREFIX) + r"[^/\s)]+/src/[^\s)]+", content)
        if sorted(bare) != sorted(url for _,url in links if "/src/" in url[len(PREFIX):]):
            raise ValueError(f"Source URL without a recognized Markdown label in {doc.name}")
        for label, url in links:
            target = url[len(PREFIX):]
            if "/src/" not in target:
                continue
            anchor = ANCHOR.fullmatch(target)
            if not anchor or anchor["pin"] != PIN:
                raise ValueError(f"Unexpected source link in {doc.name}: {url}")
            start = int(anchor["start"]) if anchor["start"] else 1
            end = int(anchor["end"] or anchor["start"]) if anchor["start"] else None
            refs[anchor["path"],start,end].add((doc.name,label))
    if not refs:
        raise ValueError("No Markdown source anchors")
    return refs


def assert_use(source, guard):
    # Mask on the entire file to handle multiline comments before the selected line.
    lines = mask_comments(source).splitlines()
    observed = " ".join(lines[guard.line-1].split())
    if observed != " ".join(guard.text.split()):
        raise ValueError(f"Missing witness use: {guard.role}")


def mutation_result(data, guard):
    source = data.decode("utf8")
    assert_use(source, guard)
    lines = source.splitlines(keepends=True)
    current = lines[guard.line-1]
    if current.count(guard.before) != 1:
        raise ValueError(f"Mutation target is ambiguous: {guard.role}")
    # Move the original line into a comment as bait; only the actual application changes.
    lines[guard.line-1] = current.rstrip().replace(guard.before,guard.after) + " -- " + current
    try:
        assert_use("".join(lines),guard)
    except ValueError:
        return {"role":guard.role,"path":AA+guard.file,"line":guard.line,
                "baseline":"matched","replace":guard.before,"with":guard.after,
                "control":"rejected, including original call as comment bait"}
    raise RuntimeError(f"Mutation escaped guard: {guard.role}")


def manifest(archive):
    citations = doc_anchors()
    tree = pinned_tree()
    files = sorted({p for p,_,_ in citations} | {AA+g.file for g in GUARDS})
    sources = {p:pinned_source(Path(p),archive,tree) for p in files}
    # Merge equivalent inclusive spans, even when one link specifies the whole file.
    spans = defaultdict(set)
    for (p,start,end),labels in citations.items():
        spans[p,start,len(sources[p].splitlines()) if end is None else end].update(labels)
    for g in GUARDS:
        spans[AA+g.file,g.line,g.line].add(("source_trace.py",g.role))
    records = []
    for (p,start,end),refs in sorted(spans.items()):
        lines = sources[p].splitlines(keepends=True)
        if not 1<=start<=end<=len(lines):
            raise ValueError(f"Invalid line range {p}:{start}-{end} for {len(lines)} lines")
        records.append({"path":p,"start":start,"end":end,"sha256":sha256(b"".join(lines[start-1:end])).hexdigest(),
                        "citations":[{"document":doc,"label":label} for doc,label in sorted(refs)]})
    return {"pin":PIN,"files":[{"path":p,"git_blob":tree[p],"sha256":sha256(sources[p]).hexdigest()} for p in files],
            "spans":records,"identity_controls":[mutation_result(sources[AA+g.file],g) for g in GUARDS]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source",type=Path,required=True,help="Root of an extracted pinned source tree")
    parser.add_argument("--out",type=Path,default=HERE/"results/source_trace.json")
    args = parser.parse_args()
    result = manifest(args.source)
    dump(args.out,result)
    print(f"{len(result['files'])} source files, {len(result['spans'])} distinct source spans, "
          f"{len(result['identity_controls'])} rejected mutations")


if __name__=="__main__":
    main()
