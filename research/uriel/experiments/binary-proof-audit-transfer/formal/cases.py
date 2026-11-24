"""Finite proof contexts for the one-lookup study. No model requests."""
from collections import defaultdict
from dataclasses import dataclass
from hashlib import sha256
from itertools import combinations, product
from math import comb


@dataclass(frozen=True)
class Candidate:
    raw: tuple
    description: str
    outcome: bool
    initial: str
    readings: tuple


@dataclass(frozen=True)
class Family:
    name: str
    split: str
    question: str
    rule: str
    initial_label: str
    menu_labels: tuple
    candidates: object
    designs: tuple


def finite_sets():
    sets = [tuple(s) for k in range(1, 4) for s in combinations(range(4), k)]
    for a, b in product(sets, repeat=2):
        outcome = len(set(a) | set(b)) >= 3
        yield Candidate((a,b), f"A={a}, B={b}", outcome, str(len(a)),
                        (len(b), int(0 in a), int(3 in b)))


def matrices():
    for a,b,c,d in product(range(1, 5), repeat=4):
        yield Candidate((a,b,c,d), f"rows ({a},{b}) and ({c},{d})",
                        a*d == b*c, str(a), (b, c, int(d%2 == 0)))


def graph_contexts():
    vertices = range(5)
    edges = list(combinations(vertices, 2))
    for k in range(1, len(edges)+1):
        for chosen in combinations(edges, k):
            incident = lambda v: sum(v in edge for edge in chosen)
            edge_list = " ".join(f"{a}-{b}" for a,b in chosen)
            yield Candidate(chosen, f"edges {edge_list}", (0,1) in chosen and (1,2) in chosen,
                            str(k), (incident(0), incident(3), int((0,2) in chosen)))


def quadratics():
    for a,b,c in product(range(1,4),range(-6,7),range(-1,8)):
        yield Candidate((a,b,c), f"(a,b,c)=({a},{b},{c})", b*b==4*a*c,
                        str(a), (abs(b), int(c%2==0), int(b>0)))


def permutations():
    edges = list(combinations(range(3),2)) + [(x,x) for x in range(3)]
    for swaps in product(edges,repeat=3):
        nontrivial = [int(a!=b) for a,b in swaps]
        image = [0,1,2]
        for a,b in reversed(swaps):
            image = [b if k==a else a if k==b else k for k in image]
        yield Candidate(swaps, "swaps "+" ".join(f"({a},{b})" for a,b in swaps),
                        sum(nontrivial)%2==1, str(swaps[0][0]),
                        (int(0==image[0]), swaps[1][0], int(swaps[2][1]==2)))


def words():
    ws=[''.join(x) for x in product('01',repeat=3)]
    def dist(a,b): return sum(x!=y for x,y in zip(a,b))
    for x,y,z in product(ws,repeat=3):
        yield Candidate((x,y,z), f"x={x}, y={y}, z={z}",
                        dist(x,z)==dist(x,y)+dist(y,z), str(x.count('1')),
                        (int(y[0]),int(z[-1]),z.count('1')))


def choose():
    for left,right in product(range(1,8),repeat=2):
        yield Candidate((left,right), f"L={left}, R={right}",
                        comb(left,2)+comb(right,2)>=12, str(left%2),
                        (right%2,int(right>3),int(left>3)))


def paired():
    for a,b,c,d in product(range(3),repeat=4):
        yield Candidate((a,b,c,d), f"left=({a},{b}), right=({c},{d})",
                        (a,b)==(c,d), str(a), (c, int(b==0), int(d==2)))


FAMILIES = [
    Family("unions","test","Is the union of A and B of cardinality at least 3?",
           "For finite sets, |A union B| + |A intersect B| = |A|+|B| (Finset.card_union_add_card_inter).",
           "number of elements of A", ("size of B","indicator that 0 belongs to A","indicator that 3 belongs to B"),
           finite_sets, (("settled",True),("lookup",False))),
    Family("determinants","test","Does the given square integer matrix have determinant zero?",
           "For a 2 by 2 matrix with rows (a,b),(c,d), its determinant equals a*d-b*c (Matrix.det_fin_two).",
           "top-left entry a", ("top-right entry b","bottom-left entry c","indicator that bottom-right entry d is even"),
           matrices, (("ambiguous",True),("settled",False))),
    Family("neighbors","test","Is vertex 1 a common neighbor of vertices 0 and 2?",
           "In a simple graph, u is in commonNeighbors(v,w) exactly if v-u and w-u are both edges (SimpleGraph.mem_commonNeighbors). The displayed edge list is complete and undirected.",
           "total edge count", ("degree of vertex 0","degree of vertex 3","indicator that edge 0-2 occurs"),
           graph_contexts, (("lookup",True),("ambiguous",False))),
    Family("quadratics","test","Is there exactly one rational number x satisfying ax^2+bx+c=0?",
           "For a nonzero leading coefficient in the rationals, a quadratic has a unique root exactly if b^2-4*a*c=0 (discrim_eq_zero_iff).",
           "leading coefficient a", ("absolute value of b","indicator that c is even","indicator that b is positive"),
           quadratics, (("lookup",False),("settled",True))),
    Family("swaps","test","Does the displayed product of three permutations have sign -1?",
           "Signs multiply under composition (Equiv.Perm.sign_mul). A swap has sign -1 if its symbols differ and +1 if they agree (Equiv.Perm.sign_swap'). For any image calculation apply the rightmost swap first.",
           "first symbol of the leftmost swap", ("indicator that the product fixes symbol 0","first symbol of the middle swap","indicator that the second symbol of the rightmost swap is 2"),
           permutations, (("settled",False),("ambiguous",False))),
    Family("hamming","test","Is the triangle inequality for x,y,z an equality, d(x,z)=d(x,y)+d(y,z)?",
           "For binary words Hamming distance counts differing coordinates. For a common intermediate word y, d(x,z)<=d(x,y)+d(y,z) (hammingDist_triangle).",
           "number of ones in x", ("first bit of y","last bit of z","number of ones in z"),
           words, (("ambiguous",True),("lookup",True))),
    Family("pairs-in-bins","dev","Do the two separate bins contain at least 12 unordered within-bin pairs in total?",
           "A bin of n distinct members contains n*(n-1)/2 unordered pairs (Nat.choose_two_right). Cross-bin pairs are excluded.",
           "remainder of L on division by two", ("remainder of R on division by two","indicator R>3","indicator L>3"),
           choose, (("settled",False),("lookup",True))),
    Family("pair-encoding","dev","Are the natural-number encodings of the two ordered pairs equal?",
           "Nat.pair_eq_pair states that encoded pairs are equal exactly if their first components agree and their second components agree.",
           "first component of left pair", ("first component of right pair","indicator left second component is 0","indicator right second component is 2"),
           paired, (("ambiguous",True),("settled",True))),
]


def key(*parts):
    return sha256(repr(parts).encode()).digest()


def select(candidates, mode, target, label):
    """Pick different candidate completions from a fixed catalog before any model run."""
    ordered = sorted(candidates, key=lambda c:key(label,'state',c.raw))
    if mode == "settled":
        hits = [c for c in ordered if c.outcome==target]
        if len(hits) >= 2: return hits[:3],hits[0]
        return None
    if mode == "ambiguous":
        shapes = defaultdict(list)
        for c in ordered: shapes[c.readings].append(c)
        for group in shapes.values():
            yes=[c for c in group if c.outcome==target]
            no=[c for c in group if c.outcome!=target]
            if yes and no: return [yes[0],no[0],*(yes[1:2] or no[1:2])],yes[0]
        return None
    for item in sorted(range(3),key=lambda i:key(label,'item',i)):
        templates=defaultdict(list)
        for c in ordered:
            templates[tuple(v for j,v in enumerate(c.readings) if j!=item)].append(c)
        for group in templates.values():
            for actual in group:
                if actual.outcome!=target: continue
                opposing=[c for c in group if c.outcome!=target and c.readings[item]!=actual.readings[item]]
                matching=[c for c in group if c.outcome==target and c!=actual and c.readings[item]==actual.readings[item]]
                if opposing:
                    return [actual,opposing[0],*(matching[:1] or opposing[1:2])],actual
    return None


def catalog(family):
    buckets=defaultdict(list)
    for c in family.candidates(): buckets[c.initial].append(c)
    for left,right in sorted(product(buckets,repeat=2), key=lambda k:key(family.name,'twins',k)):
        if left==right: continue
        groups=[select(buckets[k],mode,target,(family.name,k)) for k,(mode,target) in zip((left,right),family.designs)]
        if all(groups): return groups
    raise ValueError(f"No eligible twins for {family.name}")


def records(family):
    groups=catalog(family)
    all_states=sorted((c for group,_ in groups for c in group),key=lambda c:key(family.name,'shuffle',c.raw))
    names=['P','K','V','S','G','J']
    id_order=sorted(names,key=lambda k:key(family.name,'id',k))
    id_of={c:label for c,label in zip(all_states,id_order)}
    menu_ids=sorted(['a','b','c'],key=lambda k:key(family.name,'menu',k))
    menu=dict(sorted(zip(menu_ids,family.menu_labels)))
    states={id_of[c]:{'answer':c.outcome,'obs':{k:str(v) for k,v in zip(menu_ids,c.readings)}} for c in all_states}
    descriptions='\n'.join(f'{id_of[c]}: {c.description}.' for c in all_states)
    text=f"{family.question}\n{family.rule}\nExactly one listed candidate describes the object in this record. Read each indicator as 1 for yes and 0 for no.\n{descriptions}"
    return [dict(family=family.name,variant=str(i+1),text=text,states=states,
                 eligible=[id_of[c] for c in all_states if c.initial==actual.initial],actual=id_of[actual],
                 menu=menu,evidence=f"The {family.initial_label} is {actual.initial}.")
            for i,(_,actual) in enumerate(groups)]


def build():
    return {split:[row for family in FAMILIES if family.split==split for row in records(family)]
            for split in ['dev','test']}


if __name__=='__main__':
    for f in FAMILIES:
        for row in records(f): print(f.name,row['variant'],row['evidence'],row['eligible'],row['actual'])
