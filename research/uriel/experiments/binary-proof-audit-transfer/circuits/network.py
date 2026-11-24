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
NETWORKS = {
    "D1": "+/a/3 a/0/2 +/0/5 +/a/2/s a/0/4/t +/a/7/u",
    "D2": "+/a/4 a/0/6 a/b/2 a/c/3 b/0/7/s c/0/4/t b/c/5/u",
    "C1": "+/a/2 a/b/4 b/0/3 a/0/5 +/b/3/s a/b/2/t b/0/5/u",
    "C2": "+/a/3 a/b/4 b/c/3 c/0/2 a/c/6 +/b/2/s b/0/3/t a/0/2/u",
    "C3": "+/a/2 a/b/3 b/0/4 +/c/3 c/0/6 a/c/4 b/c/5/s +/b/2/t a/0/3/u",
    "C4": "+/a/2 a/b/4 b/c/3 c/d/2 d/0/5 b/d/4 +/c/3/s a/0/2/t b/0/3/u",
    "C5": "+/a/3 a/b/2 b/0/4 +/c/2 c/d/3 d/0/3 a/c/2 a/d/5/s b/c/2/t b/d/4/u",
    "C6": "+/a/2 a/b/5 b/c/2 c/d/3 d/e/2 e/0/4 b/d/5 +/c/3/s a/e/3/t d/0/2/u",
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
