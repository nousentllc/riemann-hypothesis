"""Compare fixed-mask neighbor counts, their Fourier energy and directional holes."""
import argparse
from fractions import Fraction
from pathlib import Path
from random import Random
import json
import numpy as np


def halves(labels, step, coset):
    n = len(labels)
    base = min(range(coset, n, step), key=labels.__getitem__)
    m = n // (2 * step)
    evens = [(base + 2*t*step) % n for t in range(m)]
    odds = [(v + step) % n for v in evens]
    return evens, odds


def checked_counts(mask, evens, odds):
    m = len(evens)
    e = [i for i, v in enumerate(evens) if v in mask]
    o = [i for i, v in enumerate(odds) if v in mask]
    # Every pair determines exactly one oriented step.
    hist = [0] * m
    for i in e:
        for j in o:
            hist[(j - i) % m] += 1
    E = np.array([v in mask for v in evens], dtype=float)
    O = np.array([v in mask for v in odds], dtype=float)
    freq = np.conjugate(np.fft.fft(E)) * np.fft.fft(O)
    inferred = np.fft.ifft(freq)
    if np.max(np.abs(inferred - hist)) > 1e-7:
        raise ValueError("FFT disagrees with exact pair differences")
    mu = Fraction(len(e)*len(o), m)
    var = Fraction(sum(j*j for j in hist), m) - mu*mu
    if abs(float(var) - np.sum(np.abs(freq[1:])**2) / m**2) > 1e-7:
        raise ValueError("Centered spectral identity failed")
    assert sum(hist) == len(e)*len(o)
    zero = Fraction(hist.count(0), m)
    # One-sided second-moment bound at zero, including a deterministic zero function.
    upper = var/(var + mu**2) if mu else Fraction(1)
    assert zero <= upper
    return hist, dict(even=len(e), odd=len(o), directions=m, zero=hist.count(0),
                      mean=str(mu), variance=str(var), variance_zero_bound=str(upper),
                      both_directions_zero=sum(j==0 and hist[-1-r]==0 for r,j in enumerate(hist)))


def exhaust():
    count = 0
    for labels in [list(range(8)), [5,0,6,2,3,7,1,4]]:
        for bits in range(256):
            mask = {t for t in range(8) if bits & 1 << t}
            for step in (1,2,4):
                for coset in range(step):
                    e,o = halves(labels,step,coset)
                    hist,_ = checked_counts(mask,e,o)
                    for r,j in enumerate(hist):
                        h = (2*r+1)*step
                        direct = sum(v in mask and (v+h)%8 in mask for v in e)
                        reverse = sum(v in mask and (v+h)%8 in mask for v in o)
                        assert j == direct and hist[-1-r] == reverse
                        count += 1
    return count


def panel(n, seed):
    rng = Random(seed)
    labels = list(range(n))
    rng.shuffle(labels)
    _, b = halves(labels, 1, 0)
    parity = b[0]%2
    e,o = halves(labels, 2, parity)
    # Least label on each mod-four child determines its mod-sixteen residue.
    a = min(e, key=labels.__getitem__)%16
    c = min(o, key=labels.__getitem__)%16
    N, k = n//16, n//128
    reservoir = rng.sample(list(range(1-parity,n,2)),N-2*k)
    fixed = set(reservoir + rng.sample(list(range(a,n,16)),k) + rng.sample(list(range(c,n,16)),k))
    diffuse = set(reservoir + rng.sample(e,k) + rng.sample(o,k))
    uniform = set(rng.sample(range(n),N))
    output = {}
    for name,mask in (("structured",fixed),("same_child_counts",diffuse),("uniform",uniform)):
        hist, row = checked_counts(mask,e,o)
        if name == "structured":
            forced = [i for i in range(len(hist)) if 2*(2*i+1)%16 not in ((a-c)%16,(c-a)%16)]
            assert len(forced) == len(hist)//2
            assert all(hist[i]==0 and hist[-1-i]==0 for i in forced)
            row["forced_bidirectional_zeros"] = len(forced)
            # Only one of the four h/2 mod 8 classes allows a forward edge.
            assert row["zero"] >= 3*len(hist)//4
        if name != "uniform":
            assert row["even"] == row["odd"] == k
        output[name] = row
    return dict(n=n,seed=seed,residues=[a,c],profiles=output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = dict(all_masks_direct_checks=exhaust(),
                  panels=[panel(n,s) for n in (4096,65536) for s in (17,71,271)])
    target = Path(__file__).with_name("directions.json")
    snapshot = json.dumps(result,indent=2) + "\n"
    if args.check:
        assert target.read_text() == snapshot
    else:
        target.write_text(snapshot)
    for p in result["panels"]:
        print(p["n"],p["seed"],[(r["zero"],r["both_directions_zero"],r["directions"])
                                   for r in p["profiles"].values()])
    print(result["all_masks_direct_checks"],"directed comparisons")


if __name__ == "__main__":
    main()
