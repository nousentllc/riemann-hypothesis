"""Cross-check the strongest saved marked-profile price certificate by literal half-mask enumeration."""
import argparse
from fractions import Fraction
import json
import math
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory


HERE = Path(__file__).resolve().parent


def leaf_prices(word, settings, cap, precision):
    adjustment = [Fraction(0) for _ in range(64)]
    for stride, residue, tangency, tip, multiplier in settings:
        u = Fraction(tangency)
        lam = Fraction(multiplier)
        assert lam >= 0 and 0 <= u <= Fraction(1, 2)
        assert 0 <= tip < 64 and tip % stride == residue
        lower_exp = sum(((2*u)**i / math.factorial(i) for i in range(40)), Fraction(0))
        factor = Fraction(math.floor(10**9 * lower_exp / 100), 10**9)
        even = (word >> (stride - 1 + residue)) & 1
        for leaf in range(residue, 64, stride):
            coefficient = int((leaf // stride) % 2 == even) - 2*factor
            if leaf == tip:
                coefficient -= (1 - 2*u) * (64 // stride) * factor / cap
            adjustment[leaf] += lam * coefficient
    return [math.ceil(precision * a) for a in adjustment]


def census(executable, word, z, scale, cap, partial, minimum, prices):
    values = [word, z, scale, cap, partial, minimum, *prices]
    raw = subprocess.check_output([executable], text=True, input=" ".join(map(str, values)) + "\n")
    rooted, uncredited, pairs, distinct = map(int, raw.split())
    return dict(threshold=z, root_hole=rooted, root_uncredited=uncredited,
                maximum=max(rooted, uncredited), root_pairs=pairs, distinct_root_supports=distinct)


def verify():
    record = json.loads((HERE/"certificate.json").read_text())
    best = min(record["uppers"], key=lambda row: row["threshold"])
    cap = Fraction(record["rate_cap"])
    assert cap.denominator == 10000
    full = cap.numerator
    partial = 64*cap.denominator - 26*full
    word, z, scale = best["word"], best["threshold"], record["scale"]
    with TemporaryDirectory() as temporary:
        exe = Path(temporary)/"census"
        subprocess.run([os.environ.get("CXX","c++"),"-std=c++17","-O3",HERE/"independent.cpp","-o",exe],check=True)
        p = leaf_prices(word,best["settings"],cap,scale)
        ceiling = census(exe,word,z,scale,full,partial,2,p)
        previous = census(exe,word,z-1,scale,full,partial,2,p)
    assert ceiling["maximum"] == best["residual"] <= 0
    assert previous["maximum"] == best["previous_tick"] > 0
    assert previous["root_pairs"] == ceiling["root_pairs"]
    assert previous["distinct_root_supports"] == ceiling["distinct_root_supports"]
    return {"word":word, "scale":scale, "half_masks_each":3263443, "rate_cap":str(cap),
            "full_slots":26, "full_slot_units":full, "partial_slot_units":partial, "price_vector":p,
            "ceiling":ceiling, "previous_grid_point":previous}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = verify()
    target = HERE/"independent.json"
    if args.write:
        target.write_text(json.dumps(result,indent=2)+"\n")
    else:
        assert result == json.loads(target.read_text())
    print(str(Fraction(result["ceiling"]["threshold"],result["scale"])),
          result["ceiling"]["maximum"],result["previous_grid_point"]["maximum"])


if __name__ == "__main__":
    main()
