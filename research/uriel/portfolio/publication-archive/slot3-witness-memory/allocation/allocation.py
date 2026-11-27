"""Exact tradeoff between guaranteed positive answers and query coverage at a fixed tag budget."""
from collections import Counter, defaultdict
from hashlib import sha256
from pathlib import Path
import argparse
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from benchmark import read_reference


def scores(labels, tags, questions):
    buckets = defaultdict(list)
    for i, tag in tags.items():
        buckets[tag].append(labels[i])
    answers = {}
    for i, tag in tags.items():
        for e in questions:
            values = {e in profile for profile in buckets[tag]}
            answers[i,e] = ("yes" if True in values else "no") if len(values)==1 else "unknown"
            if answers[i,e] != "unknown" and (answers[i,e]=="yes") != (e in labels[i]):
                raise ValueError("Unlicensed answer")
    return answers


def optimum(n, empties, capacity):
    """Minimum unknown state-query pairs for each AT LEAST s true-positive count."""
    best = [None]*(n+1)
    for singles in range(n+1):
        for inside_empty in range(n-singles+1):
            remaining = n-singles-inside_empty
            # Distribute the remaining positives over groups of size >=2.
            for groups in range(min(remaining//2, capacity-1-singles)+1):
                if groups == 0 and remaining != 0:
                    continue
                small, big_count = divmod(remaining,groups) if groups else (0,0)
                cost = (groups-big_count)*small**2 + big_count*(small+1)**2
                cost += inside_empty * (inside_empty+empties)
                for target in range(singles+1):
                    if best[target] is None or cost < best[target]:
                        best[target] = cost
    return best


def partitions(n, capacity):
    def extend(prefix, used):
        if len(prefix) == n:
            yield tuple(prefix)
        else:
            for k in range(min(used+1,capacity)):
                yield from extend(prefix + [k],max(used,k+1))
    yield from extend([],0)


def small_tests():
    cases = states = 0
    for positives, empty_count in [(1,2),(2,2),(3,2),(4,2),(4,3)]:
        n=positives+empty_count
        labels={i:frozenset([i]) if i < positives else frozenset() for i in range(n)}
        for cap in range(1,min(5,n)+1):
            best=[None]*(positives+1)
            for record in partitions(n,cap):
                ans=Counter(scores(labels,dict(enumerate(record)),range(positives)).values())
                for k in range(ans["yes"]+1):
                    if best[k] is None or ans["unknown"]<best[k]:
                        best[k]=ans["unknown"]
                states+=1
            assert best==optimum(positives,empty_count,cap), (positives,empty_count,cap,best)
            cases+=1
    return {"small_populations_and_budgets":cases,"labelled_state_partitions":states}


def design(labels, reverse=False):
    tags={}
    for i,profile in labels.items():
        if not profile:
            tags[i]=0
            continue
        e,=profile
        if reverse:
            e=65-e
        if e<=11:
            tags[i]=e
        elif e<=32:
            tags[i]=12+(e-12)//3
        else:
            tags[i]=19+(e-33)//4
    return tags


def run(repo):
    protocol_hash=sha256((HERE/"PROTOCOL.md").read_bytes()).hexdigest()
    if protocol_hash!="e3db652995f2cdf86f18695c5c80a3eff77cf8725097a75ad50c1d8d0c41b8a7":
        raise ValueError("Protocol mismatch")
    labels,reference=read_reference(repo)
    raw={i:i%27 for i in labels}
    opt=design(labels)
    assert len(set(raw.values()))==len(set(opt.values()))==27
    questions=range(1,65)
    old=scores(labels,raw,questions)
    new=scores(labels,opt,questions)
    old_counts,new_counts=Counter(old.values()),Counter(new.values())
    assert old_counts=={"unknown":192,"no":4992}
    assert new_counts=={"unknown":191,"yes":11,"no":4982}
    assert Counter(scores(labels,design(labels,reverse=True),questions).values())==new_counts
    frontier=optimum(64,17,27)
    max_pos=max(k for k,cost in enumerate(frontier) if cost is not None and cost<=old_counts["unknown"])
    assert max_pos==11 and frontier[11]==191 and frontier[12]>192
    return {"reference":reference,"protocol_sha256":protocol_hash,"small_tests":small_tests(),
        "observations":81,"queries":64,"tag_alphabet":27,"raw_residue":old_counts,
        "query_aware":new_counts,"max_yes_at_raw_coverage":max_pos,
        "raw_to_query_aware_cells":dict(Counter(old[k]+"_to_"+new[k] for k in old)),
        "min_unknown_by_at_least_positive_target":frontier}


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo",required=True,type=Path)
    print(json.dumps(run(parser.parse_args().repo),sort_keys=True,indent=2))
