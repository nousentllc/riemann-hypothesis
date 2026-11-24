"""Exact DC nodal analysis. Edges are (from, to, resistance, switch or '-')."""
from fractions import Fraction as F
from itertools import product


def network_edges(spec):
    edges = []
    for token in spec.split():
        u, v, ohms, *control = token.split("/")
        edges.append((u, v, int(ohms), control[0] if control else "-"))
    return edges


# '+' and '0' are the only fixed-voltage terminals. Every internal node
# is in the component containing both terminals in every switch setting.
HISTORICAL_NETWORKS = {
    "D1": "+/a/3 a/0/2 +/0/5 +/a/2/s a/0/4/t +/a/7/u",
    "D2": "+/a/4 a/0/6 a/b/2 a/c/3 b/0/7/s c/0/4/t b/c/5/u",
    "C1": "+/a/2 a/b/4 b/0/3 a/0/5 +/b/3/s a/b/2/t b/0/5/u",
    "C2": "+/a/3 a/b/4 b/c/3 c/0/2 a/c/6 +/b/2/s b/0/3/t a/0/2/u",
    "C3": "+/a/2 a/b/3 b/0/4 +/c/3 c/0/6 a/c/4 b/c/5/s +/b/2/t a/0/3/u",
    "C4": "+/a/2 a/b/4 b/c/3 c/d/2 d/0/5 b/d/4 +/c/3/s a/0/2/t b/0/3/u",
    "C5": "+/a/3 a/b/2 b/0/4 +/c/2 c/d/3 d/0/3 a/c/2 a/d/5/s b/c/2/t b/d/4/u",
    "C6": "+/a/2 a/b/5 b/c/2 c/d/3 d/e/2 e/0/4 b/d/5 +/c/3/s a/e/3/t d/0/2/u",
}


PREVIOUS_THRESHOLD_NETWORKS = {
    "T1": "+/a/3 a/b/4 b/0/3 +/c/4 c/0/5 b/c/3 +/0/2 +/b/5/s a/0/5/t a/c/6/u",
    "T2": "+/a/2 a/b/5 b/0/4 +/c/5 c/d/4 d/0/3 b/c/3 a/d/5 b/d/5/s +/b/3/t c/0/4/u",
    "T3": "+/a/5 a/c/3 c/0/4 +/b/3 b/d/5 d/0/2 a/b/2 c/d/5 b/c/3 a/d/3/s +/c/5/t b/0/5/u",
    "T4": "+/a/7 a/b/7 b/c/7 c/0/5 +/d/4 d/e/3 e/0/3 b/e/4 a/d/5/s c/e/4/t b/d/6/u",
    "T5": "+/a/5 a/b/2 b/c/3 c/0/3 +/d/4 d/e/2 e/0/4 b/e/5 b/d/3 a/e/4/s +/b/3/t c/d/4/u",
    "T6": "+/a/3 a/b/4 b/c/2 c/0/3 +/d/2 d/e/4 e/f/3 f/0/4 a/e/3/s b/f/4/t c/d/4/u",
}


PREVIOUS_FORCED_NETWORKS = {
    "F1": "+/a/2 a/d/9 d/c/6 b/c/2 b/0/2 0/c/2 0/d/7 c/a/9 +/b/5 +/d/3 b/d/5/s a/b/5/t c/+/3/u",
    "F2": "+/b/5 c/b/7 a/c/2 e/a/9 d/e/5 0/d/4 a/d/2 c/0/4 c/e/3 a/b/8 +/a/7/s 0/e/3/t d/+/8/u",
    "F3": "a/+/9 c/a/5 b/c/5 b/e/3 d/e/7 d/0/7 d/b/7 +/c/6 a/d/9 e/c/4 c/d/5 b/0/2/s 0/c/9/t +/d/9/u",
    "F4": "e/+/4 e/f/6 c/f/3 d/c/3 b/d/3 b/a/8 0/a/8 d/e/8 e/b/8 e/0/8/s a/d/2/t +/d/7/u",
    "F5": "+/b/7 e/b/4 e/c/6 c/d/6 f/d/5 a/f/8 a/0/3 b/c/8 f/b/8 f/c/6 f/+/7/s +/e/3/t e/a/8/u",
    "F6": "+/e/3 c/e/5 c/a/4 b/a/2 b/f/6 d/f/7 d/0/6 b/0/4 f/e/9 f/c/8 f/a/2 d/+/5/s +/a/8/t 0/a/6/u"
}


def solve(a, rhs):
    """Gauss–Jordan elimination over Fraction, without any floating arithmetic."""
    rows = [list(r) + [b] for r, b in zip(a, rhs)]
    for j in range(len(rows)):
        pivot = next(i for i in range(j, len(rows)) if rows[i][j])
        rows[j], rows[pivot] = rows[pivot], rows[j]
        scale = rows[j][j]
        rows[j] = [x / scale for x in rows[j]]
        for i, row in enumerate(rows):
            if i != j and row[j]:
                factor = row[j]
                rows[i] = [x - factor*y for x, y in zip(row, rows[j])]
    return [r[-1] for r in rows]


def model(edges, setting):
    fixed = {"+": F(12), "0": F(0)}
    nodes = sorted({s for u,v,_,_ in edges for s in (u,v)} - fixed.keys())
    index = {x:i for i,x in enumerate(nodes)}
    a = [[F(0) for _ in nodes] for _ in nodes]
    rhs = [F(0) for _ in nodes]
    for u,v,r,s in edges:
        if s != "-" and not setting[s]:
            continue
        for x,y in [(u,v),(v,u)]:
            if x not in index:
                continue
            i = index[x]
            a[i][i] += F(1,r)
            if y in index:
                a[i][index[y]] -= F(1,r)
            else:
                rhs[i] += fixed[y]/r
    voltage = dict(fixed, **dict(zip(nodes,solve(a,rhs))))
    current = [((voltage[u]-voltage[v])/r if s == "-" or setting[s] else F(0))
               for u,v,r,s in edges]
    return voltage, current


def all_states(edges):
    switches = sorted({s for *_,s in edges if s != "-"})
    states = []
    for bits in product((0,1), repeat=len(switches)):
        setting = dict(zip(switches,bits))
        volts, amps = model(edges,setting)
        readings = {"V"+x:v for x,v in volts.items() if x not in {"+","0"}}
        readings.update({"I"+str(i+1):v for i,v in enumerate(amps)})
        states.append(("".join(map(str,bits)),readings))
    return states

PREVIOUS_MARKED_NETWORKS = {'G1': '+/a/9 a/c/7 d/c/3 d/b/3 0/b/2 0/d/8 +/c/2 c/0/8 0/a/5 c/b/4 d/a/2 b/a/2/s +/d/6/t +/b/5/u', 'G2': 'd/+/9 b/d/4 b/e/7 e/a/9 a/c/9 0/c/3 e/c/8 +/c/9 d/0/3 d/c/3 a/0/9 0/e/9 b/+/3/s +/e/2/t b/a/7/u', 'G3': '+/f/5 a/f/6 a/e/2 c/e/5 b/c/9 d/b/6 d/0/2 c/+/7 d/e/2 e/b/3 b/f/9 0/b/6 c/d/4/s 0/e/9/t d/a/6/u', 'G4': 'a/+/9 a/d/2 b/d/2 g/b/6 g/c/7 f/c/7 f/e/4 0/e/2 c/b/4/s g/a/7/t g/f/9/u', 'G5': 'c/+/8 a/c/7 a/e/8 e/g/7 g/d/2 b/d/9 b/f/5 f/0/4 a/0/6 b/a/3/s d/a/2/t d/0/2/u', 'G6': 'g/+/9 g/a/3 a/f/9 f/d/2 d/b/7 b/e/4 e/c/2 0/c/8 a/c/3 f/g/7 0/a/6/s +/d/3/t g/0/4/u'}
