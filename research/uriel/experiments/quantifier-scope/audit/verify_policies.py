"""Check descriptive theory fits through disjoint-cell score distributions; no inference."""
from collections import Counter
from itertools import product

from check import ROOT, SIGS, read, require


def check(theory,audit):
    require(theory['named']==audit['policy_fit'],'Named policy score disagreement')
    patterns=theory['pattern_order']
    require(len(set(patterns))==4 and set(patterns)==set(SIGS),'Missing pattern')
    counts={p:Counter(r['signature'] for r in audit['cases'].values() if r['pattern']==p) for p in patterns}
    # A deterministic map chooses one signature per input pattern. Its joint-fit count
    # is additive over input cells. Multiplying four small polynomials counts all choices.
    hs=Counter({0:1}); optima=[]; max_hits=0
    for p in patterns:
        cell=Counter(counts[p][s] for s in SIGS)
        step=Counter()
        for previous,n in hs.items():
            for hits,m in cell.items():
                step[previous+hits]+=n*m
        hs=step
        maximum=max(counts[p][s] for s in SIGS)
        max_hits+=maximum
        optima.append([s for s in SIGS if counts[p][s]==maximum])
    require(sum(hs.values())==256,'Histogram count')
    require(theory['joint_score_histogram']=={str(k):v for k,v in hs.items()},'Histogram disagreement')
    require(max_hits==theory['best_matches'] and set(product(*optima))=={tuple(t) for t in theory['best_maps']},'Best-table disagreement')
    return max_hits,len(list(product(*optima)))


if __name__=='__main__':
    print('Reproduced nine named policies and all 256 empirical table scores. Best fit and number tied:',
          check(read(ROOT/'theory/policy_scores.json'),read(ROOT/'audit/post.json')))
