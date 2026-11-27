"""Post-hoc replay of saved trees. Independent of the training and scoring module."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import json


ROOT = Path(__file__).resolve().parent
FROZEN = "2de65ff566b1a3748708e97b89a02b14c2af2ab98342d2392b7bdba68d3682ee"
CHANNELS = ("terminal_list", "residue")
MODELS = ("plain_support", "informed_support", "informed_truth")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def fields(tag, cutoff, weight):
    # Read digits by expansion, independently of valuation/divisibility code in training.
    limit = sum(cutoff >= power for power in (3, 9, 27))
    matching = 0
    left, right = tag, weight
    while matching < 4 and left % 3 == right % 3:
        matching += 1
        left //= 3
        right //= 3
    return dict(tag=tag, cutoff=cutoff, weight=weight, power_band=limit, matching_digits=matching)


def interpret(tree, values):
    while isinstance(tree, list):
        feature, threshold, left, right = tree
        tree = left if values[feature] <= threshold else right
    return tree


def hidden_answer(center, z, e):
    modulus = next(m for m in (3, 9, 27, 81) if m > z)
    return "yes" if center % modulus == e % modulus else "no"


def supported_action(answers):
    return next(iter(answers)) if len(answers) == 1 else "abstain"


def ambiguous_terminal_tag(tag, z, e):
    """Analytic guard on visible data. Nonzero tags have singleton fibers."""
    if tag:
        return False
    modulus = next(m for m in (3, 9, 27, 81) if m > z)
    hits_in_65_to_80 = (80-e)//modulus - (64-e)//modulus
    hits = int(e % modulus == 0) + hits_in_65_to_80
    return 0 < hits < 17


def score(counts, support, truth, action):
    counts["pairs"] += 1
    counts["licensed_action"] += action == support
    counts["withheld"] += action == "abstain"
    counts["licensed_definite"] += action == support and action != "abstain"
    counts["definite_on_ambiguous"] += action != "abstain" and support == "abstain"
    counts["withheld_on_determinate"] += action == "abstain" and support != "abstain"
    counts["truth_matched"] += action == truth
    counts["wrong_on_determinate"] += support != "abstain" and action not in ("abstain", truth)
    counts["wrong_on_ambiguous"] += support == "abstain" and action not in ("abstain", truth)


def audit():
    raw = (ROOT / "results.json").read_bytes()
    require(sha256(raw).hexdigest() == FROZEN, "Original result has changed")
    prior = json.loads(raw)
    held = set(range(24,30)) | set(range(59,65))
    train = set(range(1,65)) - held
    require(set(prior["train_cutoffs"]) == train and set(prior["test_cutoffs"]) == held, "split")
    out = {"source_results_sha256": FROZEN, "channels": {}}
    for channel in CHANNELS:
        trees = prior["channels"][channel]["trees"]
        aggregate = {name:Counter() for name in (*MODELS, "informed_with_guard", "coverage_matched_rotation")}
        support_labels = {"train":Counter(), "held":Counter()}
        distinct_observations = {"train":Counter(), "held":Counter()}
        occupancy = Counter()
        per_cutoff = {z:Counter() for z in held}
        training_overlap = Counter()
        tie = Counter()
        for z in range(1,65):
            partition = "held" if z in held else "train"
            for e in range(1,z+1):
                observations = {}
                for center in range(81):
                    tag = center if channel == "residue" or 1 <= center <= 64 else 0
                    observations.setdefault(tag, []).append((center,hidden_answer(center,z,e)))
                for tag, group in observations.items():
                    values = fields(tag,z,e)
                    labels = {truth for _,truth in group}
                    support = supported_action(labels)
                    distinct_observations[partition][support] += 1
                    support_labels[partition][support] += len(group)
                    if channel == "residue" and values["matching_digits"] == 3:
                        disagree = (z <= 23) != (values["power_band"] <= 2)
                        tie[partition + "_raw_and_band_splits_disagree"] += disagree
                        tie[partition + "_three_digit_branch"] += 1
                    if partition == "train":
                        continue
                    training_overlap["seen_center_weight_pairs" if e <= max(train) else "unseen_center_weight_pairs"] += len(group)
                    if support == "abstain":
                        occupancy[str(sum(truth == "yes" for _,truth in group)) + "/" + str(len(group))] += 1
                    decisions = {name:interpret(tree,values) for name,tree in trees.items()}
                    flag = channel == "terminal_list" and ambiguous_terminal_tag(tag,z,e)
                    require(flag == (support == "abstain"), "guard versus observation enumeration")
                    rotated_e = 1 + (e-1+z//2) % z
                    rotated_flag = channel == "terminal_list" and ambiguous_terminal_tag(tag,z,rotated_e)
                    per_cutoff[z]["guard"] += int(flag) * len(group)
                    per_cutoff[z]["rotated"] += int(rotated_flag) * len(group)
                    decisions["informed_with_guard"] = "abstain" if flag else decisions["informed_support"]
                    decisions["coverage_matched_rotation"] = "abstain" if rotated_flag else decisions["informed_support"]
                    for _, truth in group:
                        for name, action in decisions.items():
                            score(aggregate[name],support,truth,action)
        require(all(n["guard"] == n["rotated"] for n in per_cutoff.values()), "per-cutoff coverage")
        for name in MODELS:
            old = prior["channels"][channel]["totals"][name]
            for new_key, old_key in (("pairs","state_queries"), ("withheld","withheld"),
                                     ("licensed_action","correct_action"), ("truth_matched","truth_correct"),
                                     ("definite_on_ambiguous","definite_on_ambiguous"),
                                     ("wrong_on_determinate","wrong_on_determinate")):
                require(aggregate[name][new_key] == old.get(old_key,0), (channel,name,new_key))
        require(aggregate["coverage_matched_rotation"]["withheld"] == aggregate["informed_with_guard"]["withheld"], "control coverage")
        out["channels"][channel] = dict(fitted_replay_and_guards=aggregate, support_state_queries=support_labels,
            distinct_observations=distinct_observations, ambiguous_yes_per_compatible_centers=occupancy,
            held_center_weight_overlap=training_overlap, residue_tree_cutoff_tie=tie, per_cutoff_guard_coverage=per_cutoff)
    return out


if __name__ == "__main__":
    print(json.dumps(audit(),sort_keys=True,indent=2))
