"""Reproducible changing-cutoff experiment. Standard-library CPU training and evaluation."""
from collections import Counter, defaultdict
from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
REGISTRATION = "6d24324f51102c1b885bdec884e4eae924ea99dad58f6d106273f08f09f472d1"
REFERENCE = "38c1523cc62195ef8309255ec572be6380ddb8bf4c4268b26df5fee7a686c8e5"
ABSTAIN, NO, YES = range(3)
NAMES = ("abstain", "no", "yes")
FEATURES = ("tag", "cutoff", "weight", "power_band", "matching_digits")
HOLDOUT = tuple(range(24, 30)) + tuple(range(59, 65))
TRAIN = tuple(z for z in range(1, 65) if z not in HOLDOUT)
CHANNELS = ("terminal_list", "residue")
MODELS = ("plain_support", "informed_support", "informed_truth")


def encode(center, channel):
    if channel == "terminal_list" and center > 64:
        return 0
    return center


def depth_of_match(a, b):
    difference = a - b
    depth = 0
    while depth < 4 and difference % 3 == 0:
        difference //= 3
        depth += 1
    return depth


def band(z):
    exponent, power = 0, 1
    while 3 * power <= z:
        exponent += 1
        power *= 3
    return exponent


def features(tag, z, e):
    return (tag, z, e, band(z), depth_of_match(tag, e))


def valuation_truth(s, z, e):
    diff = abs(s - e)
    if diff == 0:
        return YES
    multiplier = 1
    while diff % 3 == 0:
        diff //= 3
        multiplier *= 3
    return YES if multiplier > z else NO


def modular_truth(s, z, e):
    modulus = 3 ** (band(z) + 1)
    return YES if (s - e) % modulus == 0 else NO


def fibers(channel):
    groups = defaultdict(list)
    for s in range(81):
        groups[encode(s, channel)].append(s)
    return groups


def cells(channel, cutoffs):
    """Generate observation counts. The fitting caller supplies training cutoffs only."""
    groups = fibers(channel)
    for z in cutoffs:
        for e in range(1, z + 1):
            for tag, centers in groups.items():
                yes = sum(valuation_truth(s, z, e) == YES for s in centers)
                no = len(centers) - yes
                wanted = ABSTAIN if yes and no else (YES if yes else NO)
                yield features(tag, z, e), wanted, no, yes


@dataclass
class Node:
    label: int
    index: int = -1
    threshold: int = 0
    left: object = None
    right: object = None


def purity(counts):
    return sum(n*n for n in counts)


def grow(rows, indices, dimensions, depth=0):
    totals = [sum(rows[i][1][k] for i in indices) for k in range(3)]
    leaf = Node(max(range(3), key=totals.__getitem__))
    if depth >= 8 or sum(x > 0 for x in totals) == 1:
        return leaf
    n = sum(totals)
    best_num, best_den = purity(totals), n
    split = None
    for feature in range(dimensions):
        buckets = defaultdict(lambda: [0, 0, 0])
        for i in indices:
            values, counts = rows[i]
            b = buckets[values[feature]]
            for k in range(3):
                b[k] += counts[k]
        left = [0, 0, 0]
        right = list(totals)
        for threshold in sorted(buckets)[:-1]:
            for k, v in enumerate(buckets[threshold]):
                left[k] += v
                right[k] -= v
            nl = sum(left)
            nr = n - nl
            num, den = purity(left)*nr + purity(right)*nl, nl*nr
            if num*best_den > best_num*den:
                best_num, best_den = num, den
                split = (feature, threshold)
    if split is None:
        return leaf
    leaf.index, leaf.threshold = split
    left, right = [], []
    for i in indices:
        (left if rows[i][0][leaf.index] <= leaf.threshold else right).append(i)
    leaf.left = grow(rows, left, dimensions, depth+1)
    leaf.right = grow(rows, right, dimensions, depth+1)
    return leaf


def predict(node, values):
    while node.index >= 0:
        node = node.left if values[node.index] <= node.threshold else node.right
    return node.label


def serialize(node):
    if node.index < 0:
        return NAMES[node.label]
    return [FEATURES[node.index], node.threshold, serialize(node.left), serialize(node.right)]


def fit(channel):
    rows = list(cells(channel, TRAIN))
    trained = {}
    for name in MODELS:
        formatted = []
        for vals, support, no, yes in rows:
            if name.endswith("truth"):
                counts = (0, no, yes)
            else:
                counts = tuple((no+yes) if k == support else 0 for k in range(3))
            formatted.append((vals, counts))
        trained[name] = grow(formatted, list(range(len(rows))), 3 if name.startswith("plain") else 5)
    return trained


def accumulate(out, wanted, decision, no, yes):
    n = no+yes
    out["state_queries"] += n
    out["observable_query_tuples"] += 1
    out["support_"+NAMES[wanted]] += n
    out["truth_yes"] += yes
    out["truth_no"] += no
    out["support_confusion_"+NAMES[wanted]+"_to_"+NAMES[decision]] += n
    if decision == wanted:
        out["correct_action"] += n
    if decision == ABSTAIN:
        out["withheld"] += n
        return
    out["answered"] += n
    out["truth_correct"] += yes if decision == YES else no
    out["truth_wrong"] += no if decision == YES else yes
    if decision == wanted:
        out["licensed_"+NAMES[decision]] += n
    elif wanted == ABSTAIN:
        out["definite_on_ambiguous"] += n
        out["accidentally_true_on_ambiguous"] += yes if decision == YES else no
    else:
        out["wrong_on_determinate"] += n


def evaluate(channel, models):
    codebook = {s: "record-"+str((29*s+17) % 83) for s in fibers(channel)}
    assert len(codebook)==len(set(codebook.values()))
    inverse = {v:k for k,v in codebook.items()}
    systems = (*MODELS, "exact_oracle", "always_no", "always_abstain")
    total = {name:Counter() for name in systems}
    by_cutoff = {z:{name:Counter() for name in systems} for z in HOLDOUT}
    substituted = {name:Counter() for name in ("informed_support", "informed_truth", "exact_oracle")}
    original_actions = {}
    case_trace = []
    groups = fibers(channel)
    for vals, support, no, yes in cells(channel, HOLDOUT):
        tag,z,e = vals[:3]
        independent = [modular_truth(s,z,e) for s in groups[tag]]
        assert independent.count(YES)==yes
        oracle = independent[0] if min(independent)==max(independent) else ABSTAIN
        assert oracle == support
        actions = {name:predict(node, vals) for name,node in models.items()}
        actions.update(exact_oracle=oracle, always_no=NO, always_abstain=ABSTAIN)
        for name, action in actions.items():
            accumulate(total[name],support,action,no,yes)
            accumulate(by_cutoff[z][name],support,action,no,yes)
        original_actions[(tag,z,e)] = tuple(actions[name] for name in MODELS)
        if z in (26, 64) and e == 11:
            for center in sorted({0, 65}.intersection(groups[tag])):
                case_trace.append({"center":center, "cutoff":z, "weight":e, "tag":tag,
                                   "truth":NAMES[modular_truth(center,z,e)], "support":NAMES[support],
                                   "predictions":{name:NAMES[actions[name]] for name in MODELS}})
        if tag in (1,2):
            other = 3-tag
            for name,counts in substituted.items():
                dirty = modular_truth(other,z,e) if name=="exact_oracle" else predict(models[name],features(other,z,e))
                accumulate(counts,support,dirty,no,yes)
                counts["swapped_prediction_differs"] += (dirty != actions[name])*(no+yes)
                if actions[name]!=ABSTAIN and actions[name]==support and dirty!=ABSTAIN and dirty!=support:
                    counts["previously_licensed_now_wrong"] += no+yes
    # Evaluate again in different query order, consuming renamed serialized records.
    renamed = Counter()
    for z in reversed(HOLDOUT):
        for e in range(z,0,-1):
            for token in sorted(inverse,reverse=True):
                tag = inverse[token]
                vals = features(tag,z,e)
                for index,name in enumerate(MODELS):
                    assert predict(models[name],vals) == original_actions[(tag,z,e)][index]
                    renamed[name] += len(groups[tag])
    return {"totals":total, "by_cutoff":by_cutoff, "inverse_codebook_unchanged_cells":renamed,
            "valid_tag_substitution_centers_1_and_2":substituted, "case_trace":case_trace}


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    assert digest(HERE/"PROTOCOL.md")==REGISTRATION
    assert digest(HERE.parent/"research-assessment/check_cutoffs.py")==REFERENCE
    output={"registration_sha256":REGISTRATION, "assessment_census_sha256":REFERENCE,
            "train_cutoffs":TRAIN, "test_cutoffs":HOLDOUT,
            "train_state_queries":81*sum(TRAIN), "test_state_queries":81*sum(HOLDOUT),
            "channels":{}}
    for channel in CHANNELS:
        models=fit(channel)
        scores = evaluate(channel,models)
        scores["trees"]={name:serialize(node) for name,node in models.items()}
        output["channels"][channel]=scores
    return output


if __name__=="__main__":
    print(json.dumps(main(),indent=2,sort_keys=True))
