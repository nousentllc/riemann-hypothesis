"""Certified endpoint envelopes on the real primitive character modulo four."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
import json

from bands import PrimeWindow, build_cells
from chi4_closed import factors
from prime_mass import I, S, ZERO, box, log, pow_theta


@lru_cache(maxsize=65536)
def sqrt(y):
    return pow_theta(F(y), 2)


def clipped_affine(left, right, h0, h1):
    """Positive part of a rational affine chord, integrated with y^(-3/2) dy."""
    if max(h0, h1) <= 0:
        return ZERO
    m=(h1-h0)/(right-left)
    b=h0-m*left
    if min(h0,h1)<0:
        cross=-b/m
        if h0<0:
            left=cross
        else:
            right=cross
    v,w=sqrt(left),sqrt(right)
    result=(w-v).scale(2*m)+(v.reciprocal()-w.reciprocal()).scale(2*b)
    return I(max(0,result.lo),result.hi)


def enclose_piece(x,y,v,w):
    lo=clipped_affine(F(x),F(y),F(v.lo,S),F(w.lo,S))
    hi=clipped_affine(F(x),F(y),F(v.hi,S),F(w.hi,S))
    return I(lo.lo,hi.hi)


def lerp(x,a,b,u,v):
    return u.scale(F(b-x,b-a))+v.scale(F(x-a,b-a))


class EndpointEnvelope:
    """Keep the known downward jumps in phi. G - phi is convex."""
    def __init__(self, signal, left=256, right=512):
        self.signal=signal
        self.down={n:log(p).scale(F(-1,n)) for n,p in factors(right) if n%4==3 and left<n<right}
        self.up=[n for n,p in factors(right) if n%4==1 and left<n<right]

    @lru_cache(maxsize=None)
    def phi(self,y):
        result=ZERO
        for n,jump in self.down.items():
            if n<y:
                result=result+jump.scale(y-n)
        return result

    @lru_cache(maxsize=None)
    def residual(self,y):
        return self.signal.g(y)-self.phi(y)

    def envelope(self,a,b,y):
        return self.phi(y)+lerp(y,a,b,self.residual(a),self.residual(b))

    @lru_cache(maxsize=None)
    def cost(self,a,b):
        knots=[a]+[n for n in self.down if a<n<b]+[b]
        vals=[self.envelope(a,b,k) for k in knots]
        mass=ZERO
        for i in range(len(knots)-1):
            mass=mass+enclose_piece(knots[i],knots[i+1],vals[i],vals[i+1])
        return mass


def partition_cost(env, mesh):
    total=ZERO
    for a,b in zip(mesh,mesh[1:]):
        total=total+env.cost(a,b)
    return total


def optimize(env, nodes):
    n=len(nodes)
    lo={(1,0):0}; hi={(1,0):0}
    pred={}
    frontier=[]
    for k in range(2,n+1):
        for j in range(k-1,n):
            candidates=[i for i in range(j) if (k-1,i) in lo]
            costs=[env.cost(nodes[i],nodes[j]) for i in candidates]
            lo[k,j]=min(lo[k-1,i]+z.lo for i,z in zip(candidates,costs))
            high,i=min((hi[k-1,i]+z.hi,i) for i,z in zip(candidates,costs))
            hi[k,j]=high;pred[k,j]=i
        path=[]; i=n-1
        for s in range(k,1,-1):
            path.append(nodes[i]);i=pred[s,i]
        path=[nodes[0]]+path[::-1]
        q=partition_cost(env,path)
        upper=hi[k,n-1];lower=lo[k,n-1]
        assert upper==q.hi and lower<=q.lo
        frontier.append((I(lower,upper),path))
    return frontier


def first_budget(frontier, target):
    for k,(score,path) in enumerate(frontier,2):
        if score.hi<=target.lo:
            assert all(v.lo>target.hi for v,_ in frontier[:k-2])
            return {"nodes":k,"witness":path,"upper":score.pair(14),
                    "previous_lower": frontier[k-3][0].pair(14)[0] if k>2 else None}
    assert all(v.lo>target.hi for v,_ in frontier)
    return None


def geometry_mesh(env, nodes, k):
    """Choose locations without the values of G by worst unsigned jump area."""
    pts=[nodes[0],nodes[-1]]
    @lru_cache(maxsize=None)
    def cost(a,b):
        # Deterministic geometry-only strategy: integer upper envelope replacing
        # every positive jump magnitude by one and y^(-3/2) by a^(-3/2).
        w=sum((p-a)*(b-p) for p in env.up if a<p<b)
        return (sqrt(F(a)).scale(a).reciprocal().scale(F(w,2))).hi
    while len(pts)<k:
        options=[]
        for a,b in zip(pts,pts[1:]):
            for p in nodes:
                if a<p<b:
                    options.append((cost(a,b)-cost(a,p)-cost(p,b),-p))
        gain,negative=max(options);pts.append(-negative);pts.sort()
    return pts


def calculate_menu(env,nodes, truth):
    front=optimize(env,nodes)
    selected=[]
    for k,(cost,path) in enumerate(front,2):
        assert truth.lo<=cost.hi
        item={"k":k,"optimum":cost.pair(14),"ratio":(cost*truth.reciprocal()).pair(10)}
        if k in (2,3,5,9,17,33,len(nodes)):
            if (len(nodes)-1)%(k-1)==0:
                uni=nodes[::(len(nodes)-1)//(k-1)]
                item["uniform_index_ratio"]=(partition_cost(env,uni)*truth.reciprocal()).pair(10)
            blind=geometry_mesh(env,nodes,k)
            item.update(optimal_witness=path,blind_mesh=blind,
                        blind_ratio=(partition_cost(env,blind)*truth.reciprocal()).pair(10))
        selected.append(item)
    budgets={str(t):first_budget(front,box(t)) for t in map(F,("0.024","0.026","0.030"))}
    relative={str(t):first_budget(front,truth.scale(t)) for t in map(F,("1.01","1.05","1.10","1.25","1.50"))}
    return {"nodes":nodes,"edges":len(nodes)*(len(nodes)-1)//2,
            "frontier":selected,"absolute_budgets":budgets,"relative_budgets":relative}


def threshold_bounds(func, a, b, C, subdivisions=4):
    # On each subpiece f=G-C sqrt(y) is convex with f''=C/(4 y^(3/2)).
    # Its chord is an upper curve. Lower it by C*h^2/(32*x^(3/2)) for a lower curve.
    total=ZERO
    prev=F(a)
    u=func(prev)-sqrt(prev).scale(C)
    for i in range(a*subdivisions+1,b*subdivisions+1):
        y=F(i,subdivisions)
        v=func(y)-sqrt(y).scale(C)
        err=sqrt(prev).scale(prev).reciprocal().scale(C*(y-prev)**2/32)
        low=enclose_piece(prev,y,u-err,v-err)
        high=enclose_piece(prev,y,u,v)
        total=total+I(low.lo,high.hi)
        prev,u=y,v
    return total


def main():
    signal=PrimeWindow(2,build_cells())
    env=EndpointEnvelope(signal)
    truth,_=signal.between(256,512)
    assert truth.lo>0
    regular=list(range(256,513,8))
    jump=[256]+env.up+[512]
    both_pass={}
    named={str(n):(signal.g(n)*sqrt(n).reciprocal()).pair(12) for n in (256,487,512)}
    for c in map(F,("0.08","0.10","0.12","0.14")):
        passes=[]
        for n in (256,512):
            h=signal.g(n)-sqrt(n).scale(c)
            assert h.lo>0 or h.hi<0
            passes.append(h.hi<0)
        t=threshold_bounds(signal.g,256,512,c)
        cap=threshold_bounds(lambda x:env.envelope(256,512,x),256,512,c)
        assert t.hi<=cap.lo or t.hi==0
        both_pass[str(c)]={"passes":passes,"true_excess":t.pair(14),"certified_worst_excess":cap.pair(14)}
    small=regular[::4]
    front=optimize(env,small)
    exhaustive=0
    for k,(opt,path) in enumerate(front,2):
        costs=[partition_cost(env,[small[0],*interior,small[-1]])
               for interior in combinations(small[1:-1],k-2)]
        assert opt.lo==min(v.lo for v in costs) and opt.hi==min(v.hi for v in costs)
        exhaustive+=len(costs)
    controls=[]
    for a,b in ((486,488),(508,510),(488,490)):
        gt=signal.g(F(a+b,2))
        bound=env.envelope(a,b,F(a+b,2))
        difference=bound-gt
        genuine,_=signal.between(a,b)
        cost=env.cost(a,b)
        if a==508:
            assert difference.lo>0
        else:
            assert difference.lo<=0<=difference.hi
        controls.append({"a":a,"b":b,"midpoint_majorant_minus_true":difference.pair(15),
                         "majorant_mass":cost.pair(15),"true_mass":genuine.pair(15)})
    menus={"step8":calculate_menu(env,regular,truth),"upward":calculate_menu(env,jump,truth)}
    final=menus["upward"]["frontier"][-1]
    assert F(final["optimum"][0])<=F(truth.pair(14)[1]) and F(final["optimum"][1])>=F(truth.pair(14)[0])
    return {"definition":"fixed chi4, theta=1/2; endpoint chord of G-phi plus known downward curvature phi",
            "true_mass":truth.pair(14),"normalized_endpoints_and_peak":named,"downward_count":len(env.down),
            "upward_count":len(env.up),"ceilings":both_pass,"controls":controls,"brute_partitions":exhaustive,
            "menus":menus}


if __name__=="__main__":
    print(json.dumps(main(),indent=2,sort_keys=True))
