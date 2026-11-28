"""Finite controls for the order of arithmetic quantifiers and two scale margins."""
import argparse
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import hashlib

HERE = Path(__file__).resolve().parent

def host_controls():
    loose = joint = common = 0
    examples = {}
    for e0,c0,e1,c1 in product(range(4),repeat=4):
        separate = all((e0,c0,e1,c1))
        e0c0 = e0 & c0
        e1c1 = e1 & c1
        point = bool(e0c0) and bool(e1c1)
        universal = bool(e0c0 & e1c1)
        assert (not universal or point) and (not point or separate)
        loose += int(separate)
        joint += int(point)
        common += int(universal)
        if separate and not point:
            examples.setdefault('separate_but_disjoint',[e0,c0,e1,c1])
        if point and not universal:
            examples.setdefault('both_points_own_index',[e0,c0,e1,c1])
    assert (loose,joint,common)==(81,49,31)
    return {'assignments':256,'separate_existentials':loose,'same_index_each_ordinate':joint,
            'one_index_all_ordinates':common,'examples_bitmasks':examples}

def fit_controls():
    allrows = []
    for k in (2,3,5,11):
        for d in (-1,0,1):
            W = k**3+d
            xp = k**400+d
            fits = (k*W)**3 <= W**4
            cut = (k*xp)**400 <= xp**401
            assert fits == (d>=0) and cut == (d>=0)
            allrows.append(dict(k=k,offset=d,inclusion=fits,cutoff=cut))
        W = k**3
        assert (k*W)**3==W**4 and (k*W)**400>W**401
    assert (1*1)**3==1**4 and (1*1)**400==1**401
    return {'joint_offset_cases':allrows,'coverage_without_cutoff':4,'unit_boundary':'both equalities'}

def identity_and_mass_controls():
    # H1 and H2 have disjoint high sets. Pointwise replacement of the measured
    # observable would mask every violation of the common ceiling 1.
    h1,h2 = ((2,0),(0,2))
    assert all(min(pair)<=1 for pair in zip(h1,h2))
    assert all(max(h)>1 for h in (h1,h2))
    # A tent is a weighted profile after normalizing the logarithmic axis to
    # unit length; its mass is exactly height * base width / 2.
    height=F(8)
    narrow_w,broad_w = F(1,16),F(1,2)
    narrow,broad = height*narrow_w/2,height*broad_w/2
    assert narrow<1<broad and height>1
    return {'fixed_targets':[h1,h2], 'pointwise_lower_envelope':[min(k) for k in zip(h1,h2)],
            'ceiling':1,'tent_height':str(height),'tent_widths':[str(narrow_w),str(broad_w)],
            'tent_positive_areas':[str(narrow),str(broad)],'normalized_budget':'1'}

def verify_sources(root):
    sources=json.loads((HERE/'arithmetic_sources.json').read_text())
    for item in sources['files']:
        data=(root/item['path']).read_bytes()
        if hashlib.sha256(data).hexdigest()!=item['sha256']:
            raise ValueError(item['path'])
        lines=data.splitlines(keepends=True)
        for span in item['spans']:
            excerpt=b''.join(lines[span['start']-1:span['end']])
            if hashlib.sha256(excerpt).hexdigest()!=span['sha256']:
                raise ValueError(span['url'])
    return len(sources['files'])

def run():
    return {'host_quantifiers':host_controls(),'scale_margins':fit_controls(),'observables_and_mass':identity_and_mass_controls()}

if __name__=='__main__':
    if not __debug__:raise SystemExit('Use Python without -O.')
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--source',type=Path)
    args=ap.parse_args()
    result=run()
    if args.source:result['authenticated_source_files']=verify_sources(args.source)
    print(json.dumps(result,sort_keys=True,indent=2))
