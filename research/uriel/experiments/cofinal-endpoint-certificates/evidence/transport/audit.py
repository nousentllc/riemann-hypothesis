"""Verify whole pinned files and the exact line spans used in the transport argument."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

PIN = "40e56bab026552e089d7afcfeff08d2defb9c005"
HERE = Path(__file__).resolve().parent
CB = "Development/AutomorphicArithmetic/CharacterBoxes/"
PC = "Development/AutomorphicArithmetic/PrimitiveCosets/"
GI = "Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/"
GT = "Development/AbelianVarietyTheory/Definitions/GlobalTwisting/"
TS = "Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/"
SC = "Formalism/SharpRestriction/"
FG = SC+"RamificationFrobenius/TotientGaloisClasses/"

SPANS = {
    CB+"ExistsPageN": [(39,48), (50,62)],
    CB+"PairGood": [(20,34), (41,42)],
    CB+"TwistForm": [(19,26)],
    CB+"WinPairs": [(5,35), (36,55), (56,81)],
    CB+"FieldChi": [(20,30),(43,58)], CB+"OrdAny": [(86,107)],
    "Development/AutomorphicArithmetic/ShortNorms/supplyOfAdmOf": [(13,32), (48,63), (93,98), (110,135)],
    CB+"HostOfField": [(17,23)], CB+"SupplyChi": [(8,16)],
    GT+"ThinScalesIffHostBound": [(118,125)],
    CB+"Supply": [(14,26), (38,43)],
    CB+"SmallestPrimePolynomialBound": [(63,72)], CB+"HostWW": [(27,43),(49,67),(73,87)],
    CB+"KitS": [(24,40)], CB+"DesignS": [(21,42),(47,58),(89,98)],
    GI+"ExistsFamPOfKits": [(13,34),(58,69),(159,172)],
    GT+"AuxiliaryPrimeMemAvoidedPrimes": [(145,152)],
    CB+"ObjCTrue": [(30,36)], CB+"ClassSel": [(14,28)],
    TS+"NonemptyHypsOfAllRows": [(49,60)], GI+"WorkingClassesFrozen": [(21,32)],
    "Formalism/LocalToGlobal/ClassOfRecordOfChoice": [(40,49)],
    SC+"DesignExistsOfChoices": [(22,26),(54,68)], TS+"LinkEx": [(15,36)],
    TS+"ShapeOf": [(24,32)], TS+"TopShape": [(33,39),(47,55)],
    CB+"DesWin": [(11,31)], TS+"TopPlug": [(12,18)], CB+"ZeroFreeAllOfTopG": [(12,33)],
    PC+"LevelGmLeOnFamilyScales": [(13,30)], PC+"WindowInequalityOfArtinInputs": [(11,25)],
    PC+"LevelFamily": [(27,52)], PC+"GzEq": [(6,15)],
    FG+"PrimePairSizeCondition": [(7,24)],
    "Development/AutomorphicArithmetic/ShortNorms/Primes": [(1,7)],
    "Development/AutomorphicArithmetic/ShortNorms/hostOfFieldOf": [(11,31)],
    "Development/AutomorphicArithmetic/CoprimeRanks/AdmChi": [(11,24)], PC+"CoreGm": [(12,25)], FG+"TopWin": [(23,35),(66,78)],
    FG+"ExplicitFormulaErrorOfHostConditions": [(29,41),(102,125)],
}


def snapshot(source, git=None):
    entries=[]
    for mod, ranges in SPANS.items():
        rel="src/"+mod+".lean"
        data=(source/rel).read_bytes()
        lines=data.splitlines(keepends=True)
        blob=hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()
        if git:
            got=subprocess.check_output(["git","-C",str(git),"ls-tree",PIN,"--",rel],text=True).split()
            if len(got)!=4 or got[2]!=blob or got[3]!=rel:
                raise ValueError("pinned Git object differs: "+rel)
        spans=[]
        for a,b in ranges:
            if not (1<=a<=b<=len(lines)):
                raise ValueError((rel,a,b,len(lines)))
            spans.append({"lines":[a,b],"sha256":hashlib.sha256(b"".join(lines[a-1:b])).hexdigest(),
                          "url":"https://github.com/nousentllc/riemann-hypothesis/blob/"+PIN+"/"+rel+f"#L{a}-L{b}"})
        entries.append({"path":rel,"git_blob":blob,"sha256":hashlib.sha256(data).hexdigest(),"spans":spans})
    return {"pin":PIN,"files":len(entries),"spans":sum(len(e["spans"]) for e in entries),"entries":entries}


if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source",required=True,type=Path)
    ap.add_argument("--git",type=Path,help="also verify all blob identities against this checkout's pinned commit")
    ap.add_argument("--register",action="store_true",help="emit complete manifest after validation against Git")
    args=ap.parse_args()
    if args.register and not args.git:
        ap.error("--register requires --git")
    table=snapshot(args.source,args.git)
    if args.register:
        print(json.dumps(table,indent=2))
    else:
        if table!=json.loads((HERE/"source_map.json").read_text()):
            raise ValueError("source audit differs")
        print(json.dumps({k:table[k] for k in ("pin","files","spans")},indent=2))
