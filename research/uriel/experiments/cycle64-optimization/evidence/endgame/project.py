"""Project both adverse masks and check the constructive corner of the uniform-rate game."""
import argparse
from fractions import Fraction as F
from importlib.util import module_from_spec, spec_from_file_location
import json
from pathlib import Path


HERE=Path(__file__).resolve().parent
WORD=2549776587809433532
MASKS=(1230983613671479063,1518083709116552983)


def load(name,path):
    spec=spec_from_file_location(name,path)
    mod=module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


root=load('rootmark_transfer',HERE.parent/'rootmark'/'verify.py')
frozen=load('frozen_corner_transfer',HERE.parent/'rates'/'verify.py')


def exact_coefficients(mask):
    sites={j for j in range(64) if mask>>j&1}
    p,q,groups=root.node_data(WORD,sites)
    odd,preferred,_=next(r for r in groups if r[2]==32 and r[0][0]%2==1)
    assert set(preferred)=={27} and (p[27],q[27])==(0,65) and (p[46],q[46])==(0,33)
    sparse=set(odd)-{27}
    other=sites-{27,46}
    assert len(other)==26 and sparse=={1,9,17,21,33}
    checked=[]
    for pivot in [F(1,10),F(11,100)]:
        costs={i:p[i]-pivot*(q[i]-33) for i in other}
        ratios=[costs[i]-(32*pivot/15 if i in sparse else 0) for i in other]
        assert min(ratios)>0
        checked.append(str(min(ratios)))
    ps=sum(p[i] for i in other);qs=sum(q[i]-33 for i in other)
    assert ps==116 and qs==(262 if mask==MASKS[0] else 254)
    return dict(mask=mask,sites=sorted(sites),singleton=27,residual_site=46,
                sparse_productive=sorted(sparse),sum_p=ps,sum_q_minus_33=qs,
                minimum_dual_slack_at_endpoints=checked,
                leaf_rows=[[t,p[t],q[t]] for t in sorted(sites)])


def check_corner(mode,cl,cu,bl,bu):
    def z(c,b,k):
        return 116*c/(2112+k*c+32*b)
    beta=frozen.HALF if mode=='source_prefactor' else frozen.BETA
    assert frozen.tile_interval(cl,cl/2,beta)[0]>0
    assert frozen.tile_interval(cu,cu/2,beta)[1]<0
    assert frozen.sparse_anchor(cl,bl)[1]<0 and frozen.sparse_anchor(cu,bu)[0]>0
    assert F(1,10)<z(cl,bu,262)<z(cu,bl,262)<z(cl,bu,254)<z(cu,bl,254)<F(11,100)
    assert z(cl,bu,254)>F(10118,100000)
    # dB/dS=B/(16-B) on the increasing small-b branch for S in [0,5C].
    assert bu < F(71,100) and bu/(16-bu)<F(1,15)
    assert z(cu,bl,254)<frozen.all_ordinary()[1]
    # Prove the 21 other slack margins on the whole rectangle, including the irrational corner.
    forms=set()
    for ds in frozen.DELETIONS:
        forms.update(frozen.forms(frozen.groups(frozen.HARD,True,True,ds)))
    special={((1,0,0),(F(1,2),0,0)),((F(5,32),F(1,32),0),(0,F(1,32),0))}
    assert len(forms)==23 and special<=forms
    lo=cl,bl,64-26*cu-bu
    hi=cu,bu,64-26*cl-bl
    slack=min(frozen.tile_interval(frozen.dot(m,hi),frozen.dot(v,lo))[0] for m,v in forms-special)
    assert slack>0
    # On an active form the limiting base is exactly 1. Its actual power-product
    # equals 1/sqrt(nu). At both exceptional types this exceeds every literal prefactor.
    if mode=='source_prefactor':
        for nu in (cu/2,bu/32):
            assert nu*F(54,67)**2<1
    return dict(mode=mode,C=[str(cl),str(cu)],B=[str(bl),str(bu)],
                mask_upper_intervals={str(m):[str(z(cl,bu,d)),str(z(cu,bl,d))]
                                      for m,d in zip(MASKS,(262,254))},
                value_interval=list(map(str,(z(cl,bu,254),z(cu,bl,254)))),
                percent_interval=[float(100*z(cl,bu,254)),float(100*z(cu,bl,254))],
                robust_strict_forms=len(forms-special),lower_bound_on_other_log_slack=float(slack))

def results():
    limiting=json.loads((HERE.parent/'marked'/'limit_corner.json').read_text())
    ledger=json.loads((HERE.parent/'rootmark'/'near.json').read_text())
    threshold=F(ledger['threshold_numerator'],ledger['threshold_denominator'])
    assert ledger['word']==WORD and threshold==F(5059,50000)
    run=next(r for r in ledger['censuses'] if F(r['rate_cap'])==F(23921,10000))
    assert run['root_hole']<0 and run['best_other_uncredited']<0
    assert set(map(int,run['positive_uncredited_support_surpluses']))==set(MASKS)
    return dict(word=WORD,census_threshold=str(threshold),masks=[exact_coefficients(m) for m in MASKS],
                corners=[check_corner('standard',frozen.CL,frozen.CU,frozen.BL,frozen.BU),
                         check_corner('source_prefactor',*(F(v) for k in ('C_interval','B_interval')
                                                         for v in limiting[k]))])


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args();obj=results();path=HERE/'projection.json'
    if args.write:
        path.write_text(json.dumps(obj,indent=2)+'\n')
    else:
        assert obj==json.loads(path.read_text())
    for corner in obj['corners']:
        print(corner['mode'],corner['percent_interval'],corner['lower_bound_on_other_log_slack'])


if __name__=='__main__':
    main()
