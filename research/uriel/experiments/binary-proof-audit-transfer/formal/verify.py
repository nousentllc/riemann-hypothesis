"""Authenticate source declarations, audit observability, and replay actual finite specializations."""
import argparse
from hashlib import sha1, sha256
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from cases import FAMILIES, catalog, records
from check_views import audit_views

HERE = Path(__file__).resolve().parent
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"
LEAN_PIN = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
SOURCES = {
 "unions": ("Mathlib/Data/Finset/Card.lean",[(558,562,"card_union_add_card_inter")]),
 "determinants": ("Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean",[(807,815,"det_fin_two")]),
 "neighbors": ("Mathlib/Combinatorics/SimpleGraph/Basic.lean",[(915,919,"mem_commonNeighbors")]),
 "quadratics": ("Mathlib/Algebra/QuadraticDiscriminant.lean",[(99,115,"discrim_eq_zero_iff")]),
 "swaps": ("Mathlib/GroupTheory/Perm/Sign.lean",[(365,368,"sign_mul"),(389,395,"sign_swap'")]),
 "hamming": ("Mathlib/InformationTheory/Hamming.lean",[(40,42,"hammingDist"),(59,66,"hammingDist_triangle")]),
 "pairs-in-bins": ("Mathlib/Data/Nat/Choose/Basic.lean",[(110,116,"choose_two_right")]),
 "pair-encoding": ("Mathlib/Data/Nat/Pairing.lean",[(36,39,"def pair "), (79,83,"pair_eq_pair")])
}

HEADER = """import Mathlib

namespace FormalAuditPanel

def packetGraph (edges : Finset (ℕ × ℕ)) : SimpleGraph ℕ where
  Adj a b := a ≠ b ∧ ((a,b) ∈ edges ∨ (b,a) ∈ edges)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

"""

def checked(command, **kwargs):
    r = subprocess.run(command,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,**kwargs)
    if r.returncode: raise ValueError(r.stdout)
    return r.stdout.strip()

def digest(raw): return sha256(raw).hexdigest()

def authenticate(checkout):
    assert checked(['git','-C',checkout,'rev-parse','HEAD'])==PIN
    sources={}
    for name,(path,spans) in SOURCES.items():
        raw = (checkout/path).read_bytes()
        blob=checked(['git','-C',checkout,'rev-parse',PIN+':'+path])
        assert sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blob
        lines=raw.splitlines(keepends=True)
        rows=[]
        for start,end,needle in spans:
            part=b''.join(lines[start-1:end])
            assert needle.encode() in part, (name,needle)
            rows.append({'lines':[start,end],'anchor':needle,'sha256':digest(part),
            'link':f'https://github.com/leanprover-community/mathlib4/blob/{PIN}/{path}#L{start}-L{end}'})
        sources[name]=dict(path=path,blob=blob,sha256=digest(raw),spans=rows)
    return sources

def fset(values,typ):
    return "({"+",".join(str(v) for v in values)+"} : Finset "+typ+")"

def proof(f,c):
    r=c.raw
    if f.name=='unions':
        a,b=(fset(t,'ℕ') for t in r)
        claim=f"({a} ∪ {b}).card ≥ 3"
        tactic="by decide"
    elif f.name=='determinants':
        a,b,g,d=r
        claim=f"Matrix.det (!![{a},{b};{g},{d}] : Matrix (Fin 2) (Fin 2) ℤ) = 0"
        tactic="by norm_num [Matrix.det_fin_two]"
    elif f.name=='neighbors':
        edges=fset([f'({a},{b})' for a,b in r],'(ℕ × ℕ)')
        claim=f"1 ∈ (packetGraph {edges}).commonNeighbors 0 2"
        tactic="by simp [SimpleGraph.mem_commonNeighbors, packetGraph] <;> decide" 
    elif f.name=='quadratics':
        a,b,g=r
        claim=f"∃! x : ℚ, ({a}:ℚ) * (x*x) + ({b}:ℚ)*x + ({g}:ℚ)=0"
        relation=f"discrim_eq_zero_iff (a:=({a}:ℚ)) (b:=({b}:ℚ)) (c:=({g}:ℚ)) (by norm_num)"
        tactic=f"by rw [← {relation}]; norm_num [discrim]"
    elif f.name=='swaps':
        terms=[f"(Equiv.swap ({a}:Fin 3) ({b}:Fin 3))" for a,b in r]
        claim=f"Equiv.Perm.sign ({' * '.join(terms)}) = -1"
        tactic="by norm_num [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap'] <;> decide"
    elif f.name=='hamming':
        x,y,z=[f"(![{','.join(s)}] : Fin 3 → ℕ)" for s in r]
        claim=f"hammingDist {x} {z} = hammingDist {x} {y} + hammingDist {y} {z}"
        tactic="by decide"
    elif f.name=='pairs-in-bins':
        a,b=r
        claim=f"12 ≤ Nat.choose {a} 2 + Nat.choose {b} 2"
        tactic="by decide"
    elif f.name=='pair-encoding':
        a,b,g,d=r
        claim=f"Nat.pair {a} {b} = Nat.pair {g} {d}"
        tactic="by decide"
    else: raise ValueError(f.name)
    return (claim if c.outcome else f'¬ ({claim})'),tactic

def write_module():
    parts=[HEADER];names=[]
    for family in FAMILIES:
        rows=records(family)
        # Map printed candidate descriptions, which correspond one-to-one to the formal models.
        for group,_ in catalog(family):
            for c in group:
                identifier=next(line.split(':',1)[0] for line in rows[0]['text'].splitlines()
                                if line.endswith(': '+c.description+'.'))
                name=family.name.replace('-','_')+'_'+identifier
                assert c.outcome == rows[0]['states'][identifier]['answer']
                statement,tactic=proof(family,c)
                parts.append(f'theorem {name} : {statement} := {tactic}\n')
                names.append(name)
    parts.extend(f'#print axioms {name}\n' for name in names)
    parts.append('end FormalAuditPanel\n')
    return '\n'.join(parts),names

def audit():
    report={}
    for f in FAMILIES:
        twins=records(f)
        assert all(twins[0][field]==twins[1][field] for field in ('text','menu','states'))
        assert twins[0]['evidence']!=twins[1]['evidence']
        rows=[]
        for row,planned in zip(twins,f.designs):
            states=row['states']; eligible=row['eligible']; actual=row['actual']; menu=row['menu']
            assert actual in eligible and len(eligible)>1
            first={states[s]['answer'] for s in eligible}
            effective=[]
            for item in menu:
                value=states[actual]['obs'][item]
                left=[s for s in eligible if states[s]['obs'][item]==value]
                if len({states[s]['answer'] for s in left})==1: effective.append(item)
            mode='settled' if len(first)==1 else 'lookup' if effective else 'ambiguous'
            assert mode==planned[0] and states[actual]['answer']==planned[1],f.name
            if mode=='lookup': assert len(effective)==1
            if mode=='ambiguous': assert any(states[s]['answer']!=states[actual]['answer'] and
                                           states[s]['obs']==states[actual]['obs'] for s in eligible)
            rows.append({'variant':row['variant'],'actual':actual,'initial_models':len(eligible),
                         'type':mode,'objective_truth':states[actual]['answer'],'decisive_lookups':effective})
        report[f.name]=rows
    return report

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mathlib',type=Path,required=True)
    parser.add_argument('--sdk',type=Path,required=True)
    args=parser.parse_args()
    checkout=args.mathlib.resolve();sdk=args.sdk.resolve()
    sources=authenticate(checkout)
    (HERE/'sources.json').write_text(json.dumps({'mathlib':PIN,'files':sources},indent=2)+'\n')
    version=checked([sdk/'bin/lean','--version'])
    assert LEAN_PIN in version
    audit_rows=audit()
    views=audit_views()
    text,names=write_module()
    (HERE/'FiniteContexts.lean').write_text(text)
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp)
        (root/'FiniteContexts.lean').write_text(text)
        libs=[root,checkout/'.lake/build/lib/lean',*sorted((checkout/'.lake/packages').glob('*/.lake/build/lib/lean')),sdk/'lib/lean']
        env=dict(os.environ,LEAN_SYSROOT=str(sdk),LEAN_PATH=os.pathsep.join(map(str,libs)))
        log=checked([sdk/'bin/lean','-j1','-o','FiniteContexts.olean','FiniteContexts.lean'],cwd=root,env=env)
        replay=checked([sdk/'bin/leanchecker','-v','FiniteContexts'],cwd=root,env=env)
        assert 'replaying FiniteContexts' in replay and 'sorry' not in log and all(
            "'FormalAuditPanel."+name+"'" in log for name in names)
        dependencies=set()
        for match in re.findall(r'depends on axioms: \[([^\]]+)\]',log):
            dependencies.update(s.strip() for s in match.split(','))
        assert dependencies<= {'propext','Classical.choice','Quot.sound'}
        result={'lean':version,'mathlib':PIN,'sources':len(sources),'independently_recomputed_record_views':views,'kernel_checked_state_claims':len(names),
                'axiom_union':sorted(dependencies),'replay':replay,'source_sha256':digest(text.encode()),
                'scope':'Finite formal target propositions are kernel checked. Record views and lookup reachability are exhaustively checked in Python. Original Mathlib dependencies loaded from pinned cache.',
                'cases':audit_rows}
        (HERE/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f'{len(names)} finite model propositions replayed; {len(audit_rows)*2} record reachability checks passed.')

if __name__=='__main__': main()
