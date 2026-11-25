"""Independent finite controls for wait lengths, exceptional primes and matched dilations."""
import json
from fractions import Fraction
from pathlib import Path


def run():
    from bisect import bisect_right
    checked=0
    for n in range(1,13):
        for q in range(1,13):
            d=n*q
            points=[n+d*j for j in range(258)]
            for k in range(257):
                actual=points[bisect_right(points,k)]
                index=0 if k<n else 1+(k-n)//d
                assert actual==n*(1+q*index)
                assert 1<=actual-k<=d
                if k in points:
                    assert actual-k==d
                expected=0 if k<n else (k-n)//d+1
                assert expected==bisect_right(points,k)
                checked+=1
    example=[]
    n,q=2,6
    for k in (0,2,13,14,98,686,4802):
        j=0 if k<n else 1+(k-n)//(n*q)
        a=n
        while a<=k:
            a*=1+q
        example.append(dict(cutoff=k,progression=n*(1+q*j),geometric=a))
    periods=[]
    for h in range(5):
        modulus=2**(h+1)*3**(h+1)
        count=sum(t % 2**(h+1)!=0 and t % 3**(h+1)!=0 for t in range(1,modulus+1))
        frac=(1-Fraction(1,2**(h+1)))*(1-Fraction(1,3**(h+1)))
        assert Fraction(count,modulus)==frac
        periods.append(dict(cap=h,period=modulus,allowed=count,share=str(frac)))
    return dict(cutoffs_tested=checked,progression_example=example,illustrative_caps=periods)


if __name__=='__main__':
    import argparse
    cli=argparse.ArgumentParser()
    cli.add_argument('--write',action='store_true')
    args=cli.parse_args()
    data=json.dumps(run(),indent=2)+'\n'
    result=Path(__file__).with_suffix('.json')
    if args.write:result.write_text(data)
    elif data!=result.read_text():raise ValueError('Mismatch in witness geometry or capped residues.')
    print('Checked 37,008 cutoffs and five complete residue periods.')
