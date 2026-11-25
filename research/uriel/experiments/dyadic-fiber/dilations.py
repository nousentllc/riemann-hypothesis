"""Check the extension to even dilations by a finite divisor sum on the odd part."""
import argparse
import json
from fractions import Fraction
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def smallest_factors(limit):
    table=list(range(limit+1))
    for p in range(3,limit+1,2):
        if table[p]!=p: continue
        for n in range(p*p,limit+1,2*p):
            if table[n]==n: table[n]=p
    return table

def odd_ratio(b, smallest):
    # Compute divisors of b^2, then add their signed squared complementary divisors.
    divisors=[1]
    rest=b
    while rest>1:
        p=smallest[rest]
        exponent=0
        while rest%p==0:
            rest//=p
            exponent+=1
        divisors=[d*p**k for d in divisors for k in range(2*exponent+1)]
    square=b*b
    numerator=sum((1 if d%4==1 else -1)*(square//d)**2 for d in divisors)
    return Fraction(numerator,square*square)

def run(limit=100000):
    factors=smallest_factors(limit)
    ratios={}
    winners={}
    for a in range(1,limit+1):
        two_part=a & -a
        odd=a//two_part
        if odd not in ratios:ratios[odd]=odd_ratio(odd,factors)
        multiplier=Fraction(4*two_part**4-1,3*two_part**4)
        ratio=multiplier*ratios[odd]
        for label in ('all','even' if two_part>1 else 'odd'):
            if label not in winners or winners[label][0]>ratio:
                winners[label]=(ratio,[a])
            elif winners[label][0]==ratio:
                winners[label][1].append(a)
    assert winners['all'][1]==winners['odd'][1]==[39501]
    assert winners['even'][1]==[79002] and winners['even'][0]/winners['odd'][0]==Fraction(21,16)
    return dict(limit=limit,odd_divisor_sums=len(ratios),minima={
       label:dict(integers=indices,ratio_to_U1=str(ratio)) for label,(ratio,indices) in winners.items()})

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    result=run()
    file=ROOT/'dilations.json'
    if args.write: file.write_text(json.dumps(result,indent=2)+'\n')
    else: assert json.loads(file.read_text())==result
    print(result)
