"""Replay each finite certificate and compare independent formulations."""
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def reproduce(program, snapshot):
    output = subprocess.check_output([sys.executable, "-B", program], cwd=HERE)
    fresh = json.loads(output)
    assert fresh == json.loads((HERE/snapshot).read_bytes()), snapshot
    return fresh


def main():
    primary = reproduce("experiment.py","results.json")
    independent = reproduce("independent_check.py","oracle.json")
    large = reproduce("index_two.py","index_two.json")
    other_large = reproduce("index_two_certificate.py","index_two_independent.json")
    for label, other_label in [("single_tile","case_A"),("density","case_B")]:
        arm, other = primary[label], independent[other_label]
        assert arm["parameters"]["eligible_primes"] == other["prime_filter"]
        assert arm["swap"] == other["replacement"] and arm["coordinate_control"]
        for side, other_side in [("before","initial"),("after","edited")]:
            row = arm[side]
            assert row["size"] == other["retained_size"] and row["mod4"] == other["histogram_mod_4"]
            assert row["bad_point_count"] == other["normalized_bad_scores"][other_side]
            assert row["tile_distances"] == other["tile_symmetric_difference_counts"][other_side]
            assert [row[k] for k in ("local_window_min","local_window_max","first_max_start")] == other["window_min_max_first_argmax"][other_side]
    swaps = primary["density"]["matched_single_exchanges"]
    other_swaps = independent["case_B"]["matched_one_swap_census"]
    assert [swaps[k] for k in ("total","flipping","still_passing")] == [other_swaps[k] for k in ("all","fail","pass")]
    assert int(large["size"]) == other_large["retained_size"]
    assert list(map(int,large["exact_coset_counts"])) == [other_large["matched_even"],other_large["matched_odd"]]
    for side, other_side in [("before","initial"),("after","edited")]:
        for k in ("min","max"):
            assert large["windows_"+side][k] == other_large["short_window"][other_side][k]
    assert other_large["rank_and_density_obstruction_at_3"]["feasible_under_rank_and_density"] is False
    print("Four finite records reproduced. Independent window, tile, histogram, swap and rank-obstruction checks passed.")


if __name__ == "__main__":
    main()
