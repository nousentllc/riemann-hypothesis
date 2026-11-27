"""Census of named integral slot-3 centers when one center is reused across cutoffs."""
import json


def scale(cutoff):
    power, exponent = 1, 0
    while 3 * power <= cutoff:
        power *= 3
        exponent += 1
    return power, exponent


def valuation_exceeds(difference, exponent):
    if difference == 0:
        return True
    order = 0
    while difference % 3 == 0:
        difference //= 3
        order += 1
    return order > exponent


def run(limit=100):
    centers = range(3 * scale(limit)[0])
    prior = [0] * len(centers)
    selected = {}
    for cutoff in range(1, limit + 1):
        power, exponent = scale(cutoff)
        labels = []
        for s in centers:
            hits = [e for e in range(1, cutoff + 1) if valuation_exceeds(s - e, exponent)]
            residue = s % (3 * power)
            expected = [residue] if 1 <= residue <= cutoff else []
            assert hits == expected
            labels.append(hits[0] if hits else 0)
        profiles = {}
        for s, label in enumerate(labels):
            history = (prior[s], label)
            prior[s] = profiles.setdefault(history, len(profiles))
        assert len(set(labels)) == cutoff + 1
        assert len(profiles) == cutoff + min(power, 3 * power - cutoff)
        if cutoff in (26, 27, 64, 80, 81, 82):
            selected[cutoff] = {"one_cutoff": len(set(labels)), "all_cutoffs": len(profiles)}
    assert valuation_exceeds(65 - 11, scale(26)[1])
    assert not valuation_exceeds(0 - 11, scale(26)[1])
    assert all(not valuation_exceeds(s - e, scale(64)[1])
               for s in (0, 65) for e in range(1, 65))
    return {"consecutive_positive_cutoffs_checked": limit, "residues_enumerated": len(centers),
            "profile_counts": selected}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
