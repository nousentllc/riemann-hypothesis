"""Certify factor-two positive mass for the primitive real character modulo four.

Run python3 -B bands.py from any directory. Only standard library imports and
the two pinned sibling modules are needed. All values used in decisions are
outward fixed-point intervals or exact rational numbers.
"""
from bisect import bisect_right
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
from pathlib import Path

from chi4_closed import factors, mass_affine
from prime_mass import I, S, ZERO, beta_constants, box, log, pow_theta, prime_powers, triangular_area

FIRST, LAST, MAX_START = 256, 4096, 2048
FIXED = (256, 512, 1024, 2048, 344)
PRIOR_MASS = {2: (F('0.079460455346'), F('0.079460455347')),
              3: (F('0.014442500709'), F('0.014442500710'))}


def positive(a):
    return I(max(0, a.lo), max(0, a.hi))


def decline(interval):
    """Provide outward rational endpoints of a directed interval."""
    return F(interval.lo, S), F(interval.hi, S)


def signed_reciprocal(a):
    if a.lo > 0:
        return a.reciprocal()
    assert a.hi < 0
    return (a.scale(-1)).reciprocal().scale(-1)


def overlap(lhs, rhs):
    return max(lhs.lo, rhs.lo) <= min(lhs.hi, rhs.hi)


def times_interval(a, low, high):
    return a * I(box(low).lo, box(high).hi)


@dataclass(frozen=True)
class Cell:
    left: int
    right: int
    a: I
    b: I

    def integrate(self, left, right, j):
        if left == right:
            return ZERO, ZERO
        low, low_occ = mass_affine(F(self.a.lo, S), F(self.b.hi, S), left, right, j)
        high, high_occ = mass_affine(F(self.a.hi, S), F(self.b.lo, S), left, right, j)
        return I(max(0, low.lo), high.hi), I(low_occ.lo, high_occ.hi)


class PrimeWindow:
    def __init__(self, j, cells):
        self.j = j
        self.cells = cells
        self.knots = [cell.left for cell in cells] + [LAST]
        self.mass = [ZERO]
        self.occupied = [ZERO]
        for c in cells:
            m, o = c.integrate(F(c.left), F(c.right), j)
            self.mass.append(self.mass[-1] + m)
            self.occupied.append(self.occupied[-1] + o)

    def index(self, point):
        assert FIRST <= point <= LAST
        return min(len(self.cells) - 1, bisect_right(self.knots, point) - 1)

    @lru_cache(maxsize=None)
    def prefix(self, point):
        idx = self.index(point)
        if point == LAST:
            return self.mass[-1], self.occupied[-1]
        m, o = self.cells[idx].integrate(F(self.knots[idx]), F(point), self.j)
        return self.mass[idx] + m, self.occupied[idx] + o

    def between(self, left, right):
        ml, ol = self.prefix(left)
        mr, ore = self.prefix(right)
        return positive(mr - ml), positive(ore - ol)

    def band(self, start):
        return self.between(start, 2 * start)

    def enclosed_band(self, left, right):
        # Inclusion holds even if a critical point is only enclosed.
        ml, ol = self.between(right, 2 * left)
        mh, oh = self.between(left, 2 * right)
        return I(ml.lo, mh.hi), I(ol.lo, oh.hi)

    def g(self, point):
        return value(self.cells[self.index(point)], point)

    def rigorous_mesh(self, start):
        """Separate quadrature, by monotone envelopes of the integral weight.

        Build cells with the independent sieve; no analytic primitive, no
        root calculation, no reuse of prefix integrals.
        """
        pp = prime_powers(2 * start)
        c4, _ = beta_constants(55)
        a, b = c4, ZERO
        total = ZERO
        cuts = [start] + [n for n in sorted(pp) if start < n < 2 * start] + [2 * start]

        def add(n, aa, bb):
            weight = log(pp[n]).scale((0, 1, 0, -1)[n % 4])
            return aa + weight.scale(F(1, n)), bb + weight

        for n in pp:
            if n <= start:
                a, b = add(n, a, b)
        for left, right in zip(cuts, cuts[1:]):
            steps = max(1, (4096 * (right - left) + left - 1) // left)
            step = F(right - left, steps)
            prev = a.scale(left) - b
            x = F(left)
            for _ in range(steps):
                y = x + step
                nxt = a.scale(y) - b
                area_l = triangular_area(prev.lo, nxt.lo) * step / S
                area_h = triangular_area(prev.hi, nxt.hi) * step / S
                total += I(pow_theta(y, self.j).reciprocal().scale(area_l / y).lo,
                           pow_theta(x, self.j).reciprocal().scale(area_h / x).hi)
                x, prev = y, nxt
            if right in pp:
                a, b = add(right, a, b)
        return total

    def scan(self):
        scale = pow_theta(F(2), self.j)
        knots = sorted({F(FIRST), F(MAX_START)} |
                       {F(k) for k in self.knots if FIRST < k < MAX_START} |
                       {F(k, 2) for k in self.knots if FIRST < F(k, 2) < MAX_START})
        candidates = [(v, v, self.band(v)[0], 'knot') for v in knots]
        roots = 0
        for left, right in zip(knots, knots[1:]):
            middle = (left + right) / 2
            low = self.cells[self.index(middle)]
            high = self.cells[self.index(2 * middle)]
            # D(s) = p*s - q.
            p = high.a.scale(2) - scale * low.a
            q = high.b - scale * low.b
            dl, dr = p.scale(left) - q, p.scale(right) - q
            if min(dl.lo, dr.lo) > 0 or max(dl.hi, dr.hi) < 0:
                continue
            # Every encountered potential crossing has separated endpoint signs,
            # and a nonzero slope. Boundary ambiguity would abort this run.
            assert dl.lo > 0 and dr.hi < 0 or dr.lo > 0 and dl.hi < 0
            lower, upper = decline(q * signed_reciprocal(p))
            assert left < lower <= upper < right
            m, _ = self.enclosed_band(lower, upper)
            candidates.append((lower, upper, m, 'root'))
            roots += 1

        def extreme(is_max):
            chooser = max if is_max else min
            val = I(chooser(c[2].lo for c in candidates), chooser(c[2].hi for c in candidates))
            retained = [c for c in candidates if overlap(c[2], val)]
            lo = min(r[0] for r in retained)
            hi = max(r[1] for r in retained)
            output = {'mass': val.pair(), 'full_mass_share': (val * self.mass[-1].reciprocal()).pair(),
                      'candidate_count': len(retained), 'candidate_span': I(box(lo).lo, box(hi).hi).pair(9),
                      'candidate_types': sorted({r[3] for r in retained}),
                      'all_candidates_contain_peak': all(r[1] <= 487 <= 2*r[0] for r in retained)}
            if len(retained) == 1 and retained[0][3] == 'root':
                midpoint = (lo + hi) / 2
                low = self.cells[self.index(midpoint)]
                high = self.cells[self.index(2*midpoint)]
                end1 = (times_interval(low.a, lo, hi) - low.b)
                end2 = (times_interval(high.a, 2*lo, 2*hi) - high.b)
                output['strict_interior_extremum'] = min(end1.lo, end2.lo) > 0
                output['positive_edge_height'] = (end1*pow_theta(midpoint, self.j).reciprocal()).pair(9) if lo==hi else (
                    end1 * I(pow_theta(hi,self.j).reciprocal().lo, pow_theta(lo,self.j).reciprocal().hi)).pair(9)
            return output
        return {'breakpoints': len(knots), 'affine_roots': roots, 'candidate_count': len(candidates),
                'maximum': extreme(True), 'minimum': extreme(False)}


def value(cell, point):
    return cell.a.scale(point) - cell.b


def build_cells():
    c4, _ = beta_constants(80)
    trial = dict(factors(LAST))
    sieve = {n:p for n,p in prime_powers(LAST).items() if n % 2}
    assert trial == sieve
    a, b = c4, ZERO
    cells = []
    left = FIRST
    for n, p in sorted(trial.items()):
        if n > FIRST:
            cells.append(Cell(left, n, a, b))
            left = n
        weight = log(p).scale(1 if n % 4 == 1 else -1)
        a, b = a + weight.scale(F(1,n)), b + weight
    cells.append(Cell(left, LAST, a, b))
    return cells


def computation():
    cells = build_cells()
    results = {}
    for j in (2, 3):
        signal = PrimeWindow(j, cells)
        total = signal.mass[-1]
        ref_lo, ref_hi = PRIOR_MASS[j]
        assert box(ref_lo).lo <= total.lo <= total.hi <= box(ref_hi).hi
        peak = max(signal.g(k).lo * pow_theta(F(k), j).reciprocal().lo // S for k in signal.knots if signal.g(k).lo>0)
        tops = [k for k in signal.knots if (signal.g(k) * pow_theta(F(k),j).reciprocal()).hi >= peak]
        assert tops == [487]
        peaks = signal.g(487)*pow_theta(F(487),j).reciprocal()
        fixed = []
        part = ZERO
        for start in FIXED:
            m, o = signal.band(start)
            mesh = signal.rigorous_mesh(start)
            assert mesh.lo <= m.lo <= m.hi <= mesh.hi
            if start != 344:
                part += m
            metrics = {'start':start, 'end':2*start, 'mass':m.pair(), 'mesh':mesh.pair(9),
                       'full_mass_share':(m*total.reciprocal()).pair(),
                       'positive_duration_share':(o*log(2).reciprocal()).pair(),
                       'mean_height_when_positive':(m*o.reciprocal()).pair() if o.lo > 0 else None,
                       'peak_envelope_use':(m*(peaks*log(2)).reciprocal()).pair()}
            fixed.append(metrics)
        assert overlap(part,total)
        curve = [[s,*signal.band(F(s))[0].pair(9)] for s in range(FIRST,MAX_START+1,16)]
        results[str(F(j,4))] = {'full_mass':total.pair(), 'global_peak':peaks.pair(),
                                 'peak_ordinate':487, 'fixed_bands':fixed, 'uniform_share':'1/4',
                                 'partition_agrees':overlap(part,total), 'continuous_search':signal.scan(),
                                 'plot_grid_step_16':curve}
    return {'protocol_sha256':hashlib.sha256(Path(__file__).with_name('PROTOCOL.md').read_bytes()).hexdigest(),
            'interval_scale_bits':160, 'normalization_euler_terms':80,'open_prime_power_cells':len(cells),
            'rows':results}


if __name__ == '__main__':
    print(json.dumps(computation(), indent=2, sort_keys=True))
