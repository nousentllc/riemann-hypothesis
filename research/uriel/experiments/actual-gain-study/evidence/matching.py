"""Test simultaneous even-to-odd adjacencies in a shared product-selected mask."""
import argparse
from fractions import Fraction as F
import json
from math import ceil, prod
from pathlib import Path


def cycles(n, step, labels):
    unseen = set(range(n))
    while unseen:
        base = min(unseen, key=labels.__getitem__)
        path, v = [], base
        while v in unseen:
            unseen.remove(v)
            path.append(v)
            v = (v + step) % n
        assert v == base
        yield tuple(path)


def distribution(probs):
    coefficients = [F(1)]
    for q in probs:
        expanded = [F(0)] * (len(coefficients) + 1)
        for j, value in enumerate(coefficients):
            expanded[j] += (1 - q) * value
            expanded[j + 1] += q * value
        coefficients = expanded
    return coefficients


def mask_weights(probs):
    for mask in range(1 << len(probs)):
        weight = prod(p if mask & (1 << t) else 1-p for t, p in enumerate(probs))
        yield mask, weight


def run():
    n = 8
    labels_list = [list(range(n)), [5, 0, 6, 2, 3, 7, 1, 4]]
    rows = []
    for order, labels in enumerate(labels_list):
        for profile in ("uniform", "odd_low", "even_low"):
            rates = [F(3, 8) if (profile == "odd_low" and t % 2 or
                                   profile == "even_low" and t % 2 == 0)
                     else F(1, 2) for t in range(n)]
            samples = list(mask_weights(rates))
            assert sum(weight for _, weight in samples) == 1
            for h in range(1, n):
                for orbit in cycles(n, h, labels):
                    edges = list(zip(orbit[::2], orbit[1::2]))
                    assert len(set(t for edge in edges for t in edge)) == len(orbit)
                    ps = [rates[s] * rates[t] for s, t in edges]
                    observed = [F(0)] * (len(edges) + 1)
                    for mask, weight in samples:
                        hits = sum((mask >> s & 1) * (mask >> t & 1) for s, t in edges)
                        observed[hits] += weight
                    assert observed == distribution(ps)
                    mean = sum(ps)
                    assert mean == sum(i * q for i, q in enumerate(observed))
                    assert mean >= F(9, 32) * len(orbit) * F(1, 2)**2
                    qmax = ceil(mean / 2) - 1
                    bad = sum(observed[:qmax+1])
                    mgf_bound = 2**qmax * prod(1-p/2 for p in ps)
                    assert bad <= mgf_bound
                    rows.append(dict(order=order, profile=profile, step=h, base=orbit[0],
                                     length=len(orbit), mean=str(mean), histogram=list(map(str,observed)),
                                     failure=str(bad), markov=str(mgf_bound)))
    orbit = next(cycles(n, 1, labels_list[0]))
    edges = list(zip(orbit[::2], orbit[1::2]))
    alternating = [{t for t in orbit if t%2 == parity} for parity in (0, 1)]
    assert all(sum(t in m for m in alternating) == 1 for t in orbit)
    assert all(sum(s in m and t in m for s, t in edges) == 0 for m in alternating)
    indep = distribution([F(1,4)] * len(edges))[0]
    assert indep == F(81,256)
    # log(n) <= 17409 log(2); four extra units suffice for log(16).
    large_exponent = 4096 - 32
    assert F(9,256) * 2**large_exponent > 2*17409 + 4
    assert F(9,64) * 2**(8192-32) > 1
    mask = {0,3}
    assert sum(s in mask and t in mask for s,t in edges) == 0 and 3 in mask and 2 not in mask
    return dict(n=n, panels=len(rows), mask_orbit_evaluations=len(rows)*2**n,
                edge_free_mask=[0,3], correlated_zero_probability="1", independent_zero_probability=str(indep),
                scale_certificate=dict(epsilon="1/64",x="2^8192",min_long_orbit="2^4096",
                                       delta="2^-16", union_upper="1/16", other_family_thresholds_checked=False),
                panels_exact=rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    check = parser.parse_args().check
    result = run()
    path = Path(__file__).with_name("matching-results.json")
    serialized = json.dumps(result, indent=2) + "\n"
    if check:
        assert path.read_text() == serialized
    else:
        path.write_text(serialized)
    print(result["panels"], "exact distributions;", result["mask_orbit_evaluations"], "mask/orbit evaluations")


if __name__ == "__main__":
    main()
