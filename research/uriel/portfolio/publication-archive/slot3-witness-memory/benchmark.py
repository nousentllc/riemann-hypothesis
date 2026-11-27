"""Enumerate what a partially retained witness can license, with pinned reference labels."""
import argparse
from collections import Counter, defaultdict
from hashlib import sha1, sha256
from itertools import combinations
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
COMMIT = "4b1c9fbbfb9bc50a3f791c2c1f3d7f2adb336c87"
PATH = "research/uriel/experiments/slot-three/results/weights.json"
BLOB = "17a8fcd38b942d11f64438921237b2cbe3859f7d"
PROTOCOL = "6af1f9e2d004e40eadebb4669e57a10012d77456de3190423e4ed7b2413404ea"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_reference(repo):
    ref = COMMIT + ":" + PATH
    git = ["git", "-C", str(repo)]
    oid = subprocess.check_output(git + ["rev-parse", ref], text=True).strip()
    raw = subprocess.check_output(git + ["cat-file", "blob", ref])
    calculated = sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
    require(oid == calculated == BLOB, "Unexpected reference blob")
    doc = json.loads(raw)
    require((doc["prime"], doc["modulus"], doc["cutoff"]) == (3, 81, 64), "Unexpected field metadata")
    labels = {int(key): frozenset(values) for key, values in doc["strict_sets_by_center_residue"].items()}
    return labels, {"commit": COMMIT, "path": PATH, "blob": BLOB, "sha256": sha256(raw).hexdigest()}


def strict_scale(z):
    if not isinstance(z, int) or z < 1:
        raise ValueError("Expected a positive integer cutoff")
    level, power = 0, 1
    while 3 * power <= z:
        level, power = level + 1, 3 * power
    return level + 1, 3 * power


def valuation_labels(z):
    digits, modulus = strict_scale(z)

    def near(s, e):
        difference = abs(s - e)
        if difference == 0:
            return True
        valuation = 0
        while difference % 3 == 0:
            difference //= 3
            valuation += 1
        return valuation >= digits

    return {s: frozenset(e for e in range(1, z + 1) if near(s, e)) for s in range(modulus)}


def bucket_decisions(records, z):
    """All compatible named witnesses vote. A heterogeneous bucket forces abstention."""
    counts = Counter()
    positives = defaultdict(Counter)
    for opaque_id, observation, weights in records:
        counts[observation] += 1
        positives[observation].update(weights)
    decisions = {}
    for observation, total in counts.items():
        for e in range(1, z + 1):
            votes = positives[observation][e]
            decisions[observation, e] = "no" if votes == 0 else "yes" if votes == total else "unknown"
    return decisions


def residue_decision(observed, e, retained_modulus, full_modulus):
    """Count compatible values by congruence using the observation alone."""
    if e % retained_modulus != observed:
        return "no"
    return "yes" if retained_modulus == full_modulus else "unknown"


def ratio(a, b):
    return {"numerator": a, "denominator": b, "value": round(a / b, 8) if b else None}


def metrics(records, decisions, z):
    n = Counter()
    for opaque_id, observation, weights in records:
        for e in range(1, z + 1):
            gt, answer = e in weights, decisions[observation, e]
            category = ("withheld_positive" if gt else "withheld_negative") if answer == "unknown" else {
                (True, "yes"): "true_positive", (False, "no"): "true_negative",
                (True, "no"): "false_negative", (False, "yes"): "false_positive",
            }[gt, answer]
            n[category] += 1
    counts = {key: n[key] for key in ("true_positive", "true_negative", "false_positive", "false_negative",
                                        "withheld_positive", "withheld_negative")}
    total = sum(counts.values())
    covered = total - n["withheld_positive"] - n["withheld_negative"]
    positives = n["true_positive"] + n["false_negative"] + n["withheld_positive"]
    negatives = total - positives
    return {
        "counts": counts, "coverage": ratio(covered, total),
        "positive_recall_all": ratio(n["true_positive"], positives),
        "negative_specificity_all": ratio(n["true_negative"], negatives),
        "accuracy_on_answered": ratio(n["true_positive"] + n["true_negative"], covered),
        "accuracy_with_abstention_as_miss": ratio(n["true_positive"] + n["true_negative"], total),
    }


def residue_trials(labels, z):
    digits, modulus = strict_scale(z)
    require(labels.keys() == set(range(modulus)), "Missing residues")
    by_level, previous = [], {}
    for k in range(digits + 1):
        retained = 3**k
        rows = [(s, s % retained, weights) for s, weights in labels.items()]
        decisions = bucket_decisions(rows, z)
        for (observation, e), answer in decisions.items():
            direct = residue_decision(observation, e, retained, modulus)
            require(answer == direct, "Fiber and congruence answers disagree")
            if k:
                old = previous[observation % (retained // 3), e]
                require(old == "unknown" or old == answer, "Extra evidence reversed a certified answer")
        m = metrics(rows, decisions, z)
        require(m["counts"]["false_positive"] == 0 and m["counts"]["false_negative"] == 0, "Unsound admission")
        by_level.append({"digits": k, "retained_modulus": retained, **m})
        previous = decisions
    require(by_level[-1]["coverage"]["value"] == 1, "Full residue failed to recover an answer")
    return by_level


def tag_controls(labels, z):
    queries = set(range(1, z + 1))
    types = set(labels.values())
    require(types == {frozenset()} | {frozenset({e}) for e in queries}, "Missing a possible query profile")
    code = {weights: next(iter(weights), 0) for weights in types}
    edges = 0
    for left, right in combinations(types, 2):
        require(bool(left ^ right), "Pair lacks a distinguishing query")
        edges += 1
    for weights in labels.values():
        for e in queries:
            require((code[weights] == e) == (e in weights), "Query-independent tag failed")
    binary_values = {1 in weights for weights in labels.values()}
    require(binary_values == {False, True}, "Fixed-weight responses collapsed")
    exceed = 1 << ((len(types) - 1).bit_length() - 1)
    require(exceed in queries and code[frozenset({exceed})] % exceed == code[frozenset()] % exceed,
            "Expected truncation collision absent")
    return {"fixed_weight": 1, "fixed_weight_symbols": len(binary_values),
            "fixed_weight_bits": (len(binary_values) - 1).bit_length(),
            "arbitrary_later_query_symbols": len(types), "arbitrary_later_query_bits": (len(types) - 1).bit_length(),
            "mutually_conflicting_profile_pairs": edges, "arbitrary_query_roundtrip_decisions": z * len(labels),
            "six_bit_collision_at_cutoff64": {"empty_tag": 0, "singleton_tag": exceed,
                                             "both_tags_mod_64": 0, "distinguishing_weight": exceed}}


def identity_controls(labels, z):
    full = [(s, s, weights) for s, weights in labels.items()]
    d = bucket_decisions(full, z)
    swaps = 0
    for a, b in combinations(range(1, z + 1), 2):
        require(len(labels[a]) == len(labels[b]) == 1, "Cardinality leak")
        for e in (a, b):
            require(d[a, e] != d[b, e], "Substituted record hides the expected mismatch")
        swaps += 1
    # Rename both the opaque IDs and observation labels and reverse row order.
    check_count = 0
    for k in range(strict_scale(z)[0] + 1):
        base = [(s, s % 3**k, w) for s, w in labels.items()]
        renamed = [(101 + (17 * s + 13) % 81, ("alias", -g), w) for s, g, w in reversed(base)]
        require(len({row[0] for row in renamed}) == len(labels), "ID renaming is not bijective")
        one, two = bucket_decisions(base, z), bucket_decisions(renamed, z)
        for s, g, w in base:
            for e in range(1, z + 1):
                require(one[g, e] == two[("alias", -g), e], "Identifier leaked into answer")
                check_count += 1
    cardinality_rows = [(s, len(w), w) for s, w in labels.items()]
    dc = bucket_decisions(cardinality_rows, z)
    require(all(dc[0,e] == "no" and dc[1,e] == "unknown" for e in range(1, z + 1)),
            "Set-cardinality control failed")
    require(28 not in labels[1] and abs(1 - 28) == 27, "Strict-boundary control failed")
    return {"equal_singleton_cardinality_swaps": swaps, "distinguishing_decisions_checked": 2 * swaps,
            "center_1_and_2_weight_1": [d[1,1], d[2,1]],
            "permutation_invariance_decisions": check_count,
            "observed_set_cardinality_only": metrics(cardinality_rows, dc, z),
            "known_cardinality_and_weight_1": {"empty_size": dc[0,1], "singleton_size": dc[1,1]},
            "strict_boundary": {"center": 1, "weight": 28, "distance": "1/27", "accepted": False}}


def experiment(repo):
    require(sha256((HERE / "PROTOCOL.md").read_bytes()).hexdigest() == PROTOCOL, "Registered design bytes changed")
    labels, reference = read_reference(repo)
    require(labels == valuation_labels(64), "Pinned labels differ from independent valuations")
    held_out = []
    for z in (26, 27, 28, 80, 81, 82):
        observed = valuation_labels(z)
        rates = residue_trials(observed, z)
        require(len(set(observed.values())) == z + 1, "Held-out answer profiles missing")
        held_out.append({"cutoff": z, "strict_modulus": len(observed), "profile_count": len(set(observed.values())),
                         "tested_decisions_across_levels": len(observed) * z * len(rates),
                         "unknown_by_digits": [row["counts"]["withheld_positive"] + row["counts"]["withheld_negative"]
                                               for row in rates]})
    constant = [(s, None, w) for s, w in labels.items()]
    return {"registered_protocol_sha256": PROTOCOL, "ground_truth": reference, "cutoff": 64,
            "rows": 5184, "positive_ground_truth": 64, "negative_ground_truth": 5120,
            "partial_residue_trials": residue_trials(labels, 64), "tag_bounds": tag_controls(labels, 64),
            "controls": identity_controls(labels, 64), "held_out_inputs": held_out,
            "always_no_comparator": metrics(constant, {(None,e): "no" for e in range(1,65)}, 64)}


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, default=HERE.parents[1] / "riemann-experiments")
    args = ap.parse_args()
    print(json.dumps(experiment(args.repo), indent=2, sort_keys=True, allow_nan=False))
