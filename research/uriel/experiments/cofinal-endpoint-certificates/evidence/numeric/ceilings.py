"""Robust endpoint counts from one-sided window certificates."""
from bisect import bisect_right
from fractions import Fraction as F
import json
from mesh import EndpointEnvelope, PrimeWindow, build_cells, I,S,box,sqrt,lerp,threshold_bounds


def hull(points):
    chain=[]
    for x,h in points:
        while len(chain)>=2:
            (a,f),(b,g)=chain[-2:]
            if (g-f)*(x-b) < (h-g)*(b-a):
                break
            chain.pop()
        chain.append((x,h))
    return chain


def evaluator(env, points):
    xs=[x for x,h in points]
    def value(y):
        i=min(len(xs)-2, bisect_right(xs,y)-1)
        a,f=points[i];b,g=points[i+1]
        return env.phi(y)+lerp(y,a,b, I(f,f), I(g,g))
    return value


def study(C,signal,env):
    left,right=256,512
    passed={}
    for x in set(range(256,513,8))|set(env.down):
        diff=signal.g(x)-sqrt(x).scale(C)
        assert diff.hi<0 or diff.lo>0
        passed[x]=diff.hi<0
    critical=[]
    for n,jump in env.down.items():
        k=(sqrt(n)+sqrt(left)).reciprocal()-(sqrt(n)+sqrt(right)).reciprocal()
        assert k.lo>0
        ratio=jump.scale(-1)*k.reciprocal()
        critical.append((n,ratio))
    limiting=min(critical,key=lambda nr:nr[1].hi)
    assert all(r.lo>limiting[1].hi for n,r in critical if n!=limiting[0])
    assert all(r.lo>box(C).hi for n,r in critical)
    assert passed[left] and passed[right]
    menus={}
    for name,cand in (("step8", list(range(256,513,8))),("downward",[left]+sorted(env.down)+[right])):
        samples=[x for x in cand if passed[x]]
        caps=[(x, sqrt(x).scale(C)-env.phi(x)) for x in samples]
        low=hull([(x,v.lo) for x,v in caps]);high=hull([(x,v.hi) for x,v in caps])
        assert [x for x,v in low]==[x for x,v in high]
        lv=evaluator(env,low);hv=evaluator(env,high)
        if set(env.down).issubset(samples):
            # Every interval between consecutive sampled downward knots is convex;
            # positive excess above the concave ceiling is identically zero.
            area=box(0)
        else:
            zl=threshold_bounds(lv,left,right,C)
            zh=threshold_bounds(hv,left,right,C)
            area=I(zl.lo,zh.hi)
            assert area.lo>0
        menus[name]={"observed":len(samples),"failed_samples":[x for x in cand if not passed[x]],
                     "active_hull_vertices":[x for x,v in low],
                     "worst_excess":area.pair(13)}
    return {"necessary_downward_observations":len(critical),
            "total_minimal_if_feasible":2+len(critical) if all(passed[x] for x in env.down) else None,
            "limiting_prime_power":limiting[0],"limiting_ceiling":limiting[1].pair(12),
            "both_exterior_pass": True,"menus":menus}


def run():
    signal=PrimeWindow(2,build_cells());env=EndpointEnvelope(signal)
    return {str(c):study(c,signal,env) for c in map(F,("0.12","0.14","1"))}


if __name__=="__main__":
    print(json.dumps(run(),indent=2,sort_keys=True))
