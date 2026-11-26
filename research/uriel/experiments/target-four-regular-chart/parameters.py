"""Push all readable parameter children through the hyperbolic frame modulo two successive widths."""
from itertools import product
import json

# An O element is (a,b) for a+b*pi, pi^2=2. Gaussian pairs have real and imaginary O parts.
ZERO = (0, 0)
ONE = (1, 0)
BITS = list(product(range(2), repeat=2))


def add(x,y):
    return x[0]+y[0],x[1]+y[1]


def sub(x,y):
    return x[0]-y[0],x[1]-y[1]


def mul(x,y):
    return (x[0]*y[0]+2*x[1]*y[1], x[0]*y[1]+x[1]*y[0])


def times(k,x):
    return k*x[0],k*x[1]


def reduce(x,m):
    return tuple(t%m for t in x)


def gauss(x,y):
    return sub(mul(x[0],y[0]),mul(x[1],y[1])),add(mul(x[0],y[1]),mul(x[1],y[0]))


def norm(x):
    return add(mul(x[0],x[0]),mul(x[1],x[1]))


def unit_inverse(x,m):
    a,b=x
    k=pow(a*a-2*b*b,-1,m)
    result=reduce((a*k,-b*k),m)
    assert reduce(mul(x,result),m)==ONE
    return result


def square_root(m):
    u=0
    for _ in range(m.bit_length()+1):
        u=(-1-2*u*u)%m
    c=(1+4*u)%m
    assert (c*c+7)%m==0
    return c


def labels(center,w,values):
    shifted=(sub(values[0],(center,0)),*values[1:])
    if any(t%w for x in shifted for t in x):
        return None
    return tuple(tuple(t//w%2 for t in x) for x in shifted)


def parameter_images(center,w,s,wrong_width=False):
    # Four extra guard digits exceed all divisions by 8 in the formula.
    mod=32*w
    c=square_root(mod)
    b0=(ONE,ONE)
    d0=((c,0),(2,0))
    bard=((c,0),(-2,0))
    barb=(ONE,(-1,0))
    images=[]
    for P,Q,L,M,A in product(BITS,repeat=5):
        p=(add((center,0),times(w,P)),times(w,Q))
        v=(times(w,L),times(w,M))
        U=tuple((a//2,b//2) for a,b in p)
        n=norm(U)
        numerator=sub(add(s,norm(v)),times(4,n))
        assert all(k%8==0 for k in numerator)
        r=reduce(mul(tuple(k//8 for k in numerator),unit_inverse(n,mod)),mod)
        alpha=times(w if wrong_width else w//2,A)
        offset=gauss(p,(r,alpha))
        t1=tuple(map(add,p,offset))
        t2=tuple(map(add,gauss(b0,offset),gauss(bard,v)))
        t3=tuple(map(sub,gauss(d0,offset),gauss(barb,v)))
        vec=(*t1,*t2,*t3)
        gram=ZERO
        for x in vec:
            gram=add(gram,mul(x,x))
        assert reduce(gram,8*w)==reduce(s,8*w)
        lab=labels(center,w,vec)
        if lab is not None:
            images.append(lab)
    return images


def original_children(center,w,s):
    children=set()
    for digits in product(BITS,repeat=6):
        gram=ZERO
        for j,d in enumerate(digits):
            x=add(times(w,d), (center if j==0 else 0,0))
            gram=add(gram,mul(x,x))
        # Changing a coordinate by 2w changes Gram by a multiple of 8w.
        if reduce(gram,8*w)==reduce(s,8*w):
            children.add(digits)
    return children


def run():
    cases=[(2,8,(4,0)),(2,8,(36,0)),(2,8,(4,32)),(2,8,(36,32)),
           (2,16,(4,0)),(10,16,(36,0)),(10,16,(4,0))]
    rows=[]
    for center,w,s in cases:
        expect=original_children(center,w,s)
        hits=parameter_images(center,w,s)
        assert len(hits)==len(set(hits)) and set(hits)==expect
        rows.append(dict(pivot_center=center,width=w,target=s,parameter_cells=1024,
                         accepted=len(hits),distinct=len(set(hits)),direct_matches=len(expect)))
    wrong=parameter_images(2,8,(4,0),wrong_width=True)
    assert len(wrong)==1024 and len(set(wrong))==256
    return dict(rows=rows,wrong_skew_width=dict(accepted=len(wrong),distinct=len(set(wrong))))


if __name__ == "__main__":
    print(json.dumps(run(),indent=2))
