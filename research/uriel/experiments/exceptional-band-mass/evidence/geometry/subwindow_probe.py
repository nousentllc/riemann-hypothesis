"""Exact finite tests of a surviving clean subwindow under fragmented coverage."""
from fractions import Fraction as Q
import json

def inspect(u, end, bands):
    clean = []
    pos = u
    for left, right in bands:
        if not pos <= left < right <= end:
            raise ValueError("expected disjoint increasing bands inside window")
        if pos < left:
            clean.append((pos,left))
        pos = right
    if pos < end:
        clean.append((pos,end))
    m = sum((b-a for a,b in bands),Q(0))
    best = max((b/a for a,b in clean), default=Q(1))
    lower = end/(u+m)
    assert best**(len(bands)+1) >= lower
    return m, best, best**(len(bands)+1)==lower

def from_mask(mask, n):
    bands = []
    for i in range(n):
        if mask & (1<<i):
            left, right = 1+Q(i,n), 1+Q(i+1,n)
            if bands and bands[-1][1]==left:
                bands[-1]=(bands[-1][0],right)
            else:
                bands.append((left,right))
    return bands

def main():
    n=10
    tight=0
    for mask in range(1<<n):
        _,_,equal=inspect(Q(1),Q(2),from_mask(mask,n))
        tight += equal
    fragmented=[]
    for n in (4,8,16,32,64):
        u=Q(2**n)
        width=Q(1,n*n)
        bands=[(u+i*u/n,u+i*u/n+width) for i in range(1,n)]
        m,q,_=inspect(u,2*u,bands)
        assert m==(n-1)*width and q==1+Q(1,n)
        fragmented.append({"n":n,"total_length":str(m),"largest_ratio":str(q)})
    return {"grid_masks":1<<10, "equality_masks":tight,"fragmented":fragmented}
if __name__=="__main__":
    print(json.dumps(main(),indent=2))
