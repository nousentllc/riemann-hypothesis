"""Verify source paths, declaration lines and Git blobs for the descent trace."""
import argparse
from hashlib import sha1, sha256
import json
from pathlib import Path
import subprocess

ORIGINAL="40e56bab026552e089d7afcfeff08d2defb9c005"
PREVIOUS="0b9ed6f42cccf214e7e196f2e129ea1e3b1b5987"
AV="src/Development/AutomorphicArithmetic/AutomorphicVarieties/"
SPECS=[
    (ORIGINAL,AV+"QuadraticExtensions/LevelRk.lean","theorem UpperTheory.V.Two.levelRk","Finite power-quotient bound to level rank."),
    (ORIGINAL,AV+"QuadraticExtensions/LevUAnti.lean","theorem UpperTheory.V.Two.infRk","Uniform levels to rank at the tower subgroup."),
    (ORIGINAL,AV+"QuadraticExtensions/GenOfRk.lean","theorem UpperTheory.V.Two.genOfRk","Surjection on the limiting module from the bounded number of generators."),
    (ORIGINAL,AV+"NumberFieldTowers/XTwApplyApply.lean","abbrev XP","The target uses coefficient index p on the canonical algebraic closure."),
    (ORIGINAL,AV+"NumberFieldTowers/ExistsDescends.lean","theorem step0","Original signed nonzero twist and every relative layer."),
    (ORIGINAL,AV+"AdditiveValuationNorms/Descends.lean","theorem UpperTheory.V.PropA.descends","Wrapper consumes positive natural weights."),
    (ORIGINAL,AV+"AdditiveValuationNorms/GenLevel.lean","theorem UpperTheory.V.PropA.genLevel","Existence of a cyclotomic generator with root data."),
    (ORIGINAL,AV+"LayeredIsomorphisms/EquivOfRange.lean","theorem UpperTheory.V.Win.abiso","Isomorphic realizations of the same abelian descriptor."),
    (ORIGINAL,AV+"LayeredIsomorphisms/Layerex.lean","theorem UpperTheory.V.Win.layerex","Existence of a comparison layer at the given index."),
    (ORIGINAL,AV+"LayeredIsomorphisms/Layeriso.lean","theorem UpperTheory.V.Win.layeriso","Comparison of layers over isomorphic bases."),
    (ORIGINAL,AV+"GaloisLibrary/GaloisCohomologyLength/ShaLenEqShaInv.lean","theorem shaInv_congr","Transport under field equivalence."),
    (ORIGINAL,AV+"GaloisLibrary/GaloisCohomologyLength/ShaLenEqShaInv.lean","theorem shaLen_eq_shaInv","Length of any admissible local data equals the field invariant."),
    (ORIGINAL,"src/Formalism/GaloisCohomology/Statement.lean","def Sha (","Submodule of the first cohomology of the twist."),
    (ORIGINAL,"src/ReciprocityTheory/GaloisValuations/ContinuousConstSMulQuotient.lean","def Sha1","Intersection of kernels of local restriction."),
    (ORIGINAL,AV+"LengthEqAddEigen.lean","theorem shaLen_eq_add","Nonnegative plus and minus terms add to total."),
    (ORIGINAL,AV+"LengthEqAddEigen.lean","def VVat","Two requirements: finiteness and truncated sum."),
    (ORIGINAL,AV+"LayeredIsomorphisms/Vvat.lean","theorem UpperTheory.V.Win.vvat","A per-weight zero estimate supplies the real sum."),
    (ORIGINAL,AV+"LayeredIsomorphisms/SecondBound.lean","def ABound","Zero cap and empty center family are legal."),
    (ORIGINAL,AV+"PrimeSetBoundDataOfPrimitiveChar.lean","def BbAt","The cutoff and the layer are chosen by the original K."),
    (ORIGINAL,AV+"NumberFieldTowers/XTwApplyApply.lean","def cZero","Highest base root level."),
    (ORIGINAL,AV+"NumberFieldTowers/XTwApplyApply.lean","abbrev layF","Actual absolute root index cZero + m."),
    (ORIGINAL,AV+"NumberFieldTowers/LayerUniq.lean","theorem UpperTheory.V.Tower.layerUniq","Canonical relative layer satisfies the original predicate."),
    (PREVIOUS,"research/uriel/experiments/prescribed-gap-witnesses/evidence/fields/PhysicalGap.lean","theorem gapWinDatum","Assembles a physical local witness using direct estimates or screens."),
    (PREVIOUS,"research/uriel/experiments/prescribed-gap-witnesses/evidence/join/PrincipalBridge.lean","theorem twoSelections","Previous endpoint output required both moving and residual odd screens.")]


def audit(repository, source, previous):
    records=[]
    for revision, name, start, role in SPECS:
        target=f"{revision}:{name}"
        oid=subprocess.check_output(["git","-C",str(repository),"rev-parse",target],text=True).strip()
        if revision == ORIGINAL:
            data=(source/name).read_bytes()
        elif previous is not None:
            data=(previous / name.split("/prescribed-gap-witnesses/",1)[1]).read_bytes()
        else:
            data=subprocess.check_output(["git","-C",str(repository),"cat-file","blob",target])
        if sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()!=oid:
            raise ValueError("Source mismatch: "+target)
        positions=[i for i, line in enumerate(data.decode().splitlines(),1) if line.startswith(start)]
        if len(positions)!=1:
            raise ValueError("Expected one source declaration: "+start)
        records.append(dict(commit=revision,path=name,line=positions[0],declaration_prefix=start,
                            git_blob=oid,sha256=sha256(data).hexdigest(),role=role))
    return {"declared_original":ORIGINAL,"preceding_experiment":PREVIOUS,"anchors":records}

if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--git",type=Path,required=True)
    parser.add_argument("--source",type=Path,required=True,help="Original checkout containing src")
    parser.add_argument("--previous",type=Path,help="Extracted prior prescribed-gap-witnesses directory for offline operation")
    options=parser.parse_args()
    print(json.dumps(audit(options.git.resolve(),options.source.resolve(),options.previous),indent=2))
