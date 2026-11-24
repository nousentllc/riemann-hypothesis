"""Scored-only change of observable menus; original model parameters and truth are untouched."""
from copy import deepcopy

from cases import FAMILIES, build as initial_build, catalog

# The middle item below replaces one formerly constant reading. The third item is
# retained from the initial menu. Letter order is varied across source families.
MENUS = {
    "unions": {
        "b":"size of B",
        "a":"indicator that 3 belongs to A",
        "c":"indicator that 3 belongs to B",
    },
    "neighbors": {
        "a":"degree of vertex 3",
        "c":"indicator that the degree of vertex 2 exceeds 2",
        "b":"degree of vertex 0",
    },
    "quadratics": {
        "c":"absolute value of b",
        "b":"indicator that c is at least 5",
        "a":"indicator that b is positive",
    },
    "hamming": {
        "b":"last bit of z",
        "a":"indicator that y has exactly one one",
        "c":"first bit of y",
    },
}


def new_reading(family, raw):
    if family == "unions": return 3 in raw[0]
    if family == "neighbors": return sum(2 in edge for edge in raw)>2
    if family == "quadratics": return raw[2] >= 5
    if family == "hamming": return raw[1].count("1") == 1
    raise ValueError(family)


def build():
    initial=initial_build()
    result={split:[deepcopy(record) for record in rows] for split,rows in initial.items()}
    specs={family.name:family for family in FAMILIES}
    for row in result['test']:
        name=row['family']
        if name not in MENUS: continue
        old_menu=dict(row['menu'])
        new_menu=MENUS[name]
        row['menu']=dict(sorted(new_menu.items()))
        for group,_ in catalog(specs[name]):
            for candidate in group:
                state=next(line.split(':',1)[0] for line in row['text'].splitlines()
                           if line.endswith(': '+candidate.description+'.'))
                old_obs=row['states'][state]['obs']
                by_label={label:old_obs[key] for key,label in old_menu.items()}
                row['states'][state]['obs']={
                    key:by_label[label] if label in by_label else str(int(new_reading(name,candidate.raw)))
                    for key,label in sorted(new_menu.items())
                }
    return result
