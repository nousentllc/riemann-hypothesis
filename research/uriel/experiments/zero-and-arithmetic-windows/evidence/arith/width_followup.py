"""Exploratory rescaling check, a follow-up to the registered 3/2 tests."""
import json
from fractions import Fraction


def check_widths():
    """Evaluate real-power inequalities by taking positive integer powers."""
    widths = list(map(Fraction, ('3/2', '799/401', '800/401', '801/401', '2')))
    starts = [(2, power) for power in (3, 399, 400, 401, 801, 802)]
    checks = []
    for k, power in starts:
        W = k ** power
        for width in widths:
            p, q = width.as_integer_ratio()
            left = (k * W) ** p
            right = W ** (2 * q)
            observed = (left > right) - (left < right)
            difference = p * (1 + power) - 2 * q * power
            assert observed == (difference > 0) - (difference < 0)
            checks.append(dict(k=k, power=power, width=str(width), endpoint_comparison=observed))
    return dict(at_k_power_400_threshold='800/401', cases=checks,
                meaning='Sign of (kW)^p - W^(2q) computed exactly. Geometric step only.')


if __name__ == '__main__':
    print(json.dumps(check_widths(), indent=2))
