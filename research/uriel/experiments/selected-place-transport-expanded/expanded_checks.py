"""Exact controls for the second edition. No chosen places are enumerated."""

import json

HOST_CEILING = 22


def scale_control():
    exponents = [100]
    steps = []
    while True:
        a = exponents[-1]
        ceiling = 10**12 * a // 2
        power = ceiling.bit_length() - 1
        assert 2**power <= ceiling < 2**(power + 1)
        new = 100 * power
        steps.append(dict(seed_exponent=a, dyadic_exponent=power, checked_integer_ceiling=ceiling, result_exponent=new))
        if new <= a:
            break
        exponents.append(new)

    cardinality_controls = []
    for a in (exponents[0], exponents[-1]):
        min_m_power = a//2 + 1
        min_s = 22 * min_m_power
        j = 5
        while 3**(j-4) <= min_s:
            j += 1
        assert 3**(j-5) <= min_s < 3**(j-4)
        numerator = 3**(j*50) << (1099*min_m_power)
        floor = (numerator.bit_length() - 1)//50
        assert 2**(50*floor) < numerator < 2**(50*(floor+1))
        cardinality_controls.append(dict(seed_exponent=a, lower_m_power=min_m_power, minimal_tower_exponent=min_s,
                                         lower_three_power=j, exact_power_left_bits=numerator.bit_length(),
                                         strict_lower_cardinality_power=floor))
    assert exponents == [100, 4500, 5000, 5100]
    assert [c["strict_lower_cardinality_power"] for c in cardinality_controls] == [1138, 56093]
    return dict(bootstrap=steps, bounds=cardinality_controls)


def host_control():
    relaxed = []
    for size in range(1, HOST_CEILING + 1):
        for e in range(2, HOST_CEILING.bit_length()):
            if size % 2**e:
                continue
            for j in range(e+1):
                n0 = 2**j
                if size % n0 == 0:
                    o = size // n0
                    relaxed.append(dict(size=size, e=e, n0=n0, o=o))
    full = [row for row in relaxed if row["o"]**64 <= 2**row["e"]]
    assert max(r["size"] for r in relaxed) == 20
    assert full == [dict(size=a,e=e,n0=a,o=1) for e in range(2,5) for a in (2**e,)]
    nontrivial_minimal_e = (2**64).bit_length() - 1
    k_minimum = 2**(nontrivial_minimal_e+1)
    prime_budget = 4*(k_minimum+6)*(k_minimum+1)+1
    assert prime_budget > 2**132
    return dict(envelope_without_coset_penalty=len(relaxed),
                signed_ceiling_without_coset_penalty=2*max(r["size"] for r in relaxed),
                full_scalar_profiles=full,
                signed_ceiling_with_all_tested_fields=2*max(r["size"] for r in full),
                nontrivial_coset_minimum_e=nontrivial_minimal_e,
                nontrivial_coset_necessary_prime_budget=str(prime_budget))


def shares_control():
    a, b = (0,1), (0,2)
    # Fourier values in Z[i], each a pair for the real and imaginary integer parts.
    units = [(1,0), (0,1), (-1,0), (0,-1)]
    read = lambda tt: [sum(units[x][axis] for x in tt) for axis in (0,1)]
    assert len(a)==len(b) and read(a)==[1,1] and read(b)==[0,0]
    minimum_collision_bits = (2**1071 // 32).bit_length() - 1
    assert minimum_collision_bits == 1066
    return dict(one_coset_counts=[len(a),len(b)], normalized_shares=[1,1],
                ambient_character_sums=[read(a),read(b)],
                guaranteed_fiber_size_at_least_power_of_two=minimum_collision_bits)


def cyclic_order_control():
    tested = []
    for s in range(17):
        log_three = 0
        while 3**(log_three+1) <= s:
            log_three += 1
        three_power = 3**(log_three+5)
        modulus = 18480 * three_power * 2**s
        generator = 1 + 18480 * three_power
        odd_part = modulus
        while odd_part % 2 == 0:
            odd_part //= 2
        assert generator % odd_part == 1
        assert (generator-1) % 32 == 16
        order = 2**s
        assert pow(generator, order, modulus) == 1
        if s:
            assert pow(generator, order//2, modulus) != 1
        tested.append(dict(tower_exponent=s, modulus=modulus, order=order))
    return tested


def main():
    print(json.dumps(dict(
        readable_scale=scale_control(),
        old_host=host_control(),
        one_coset=shares_control(), cyclic_order=cyclic_order_control()),indent=2))


if __name__ == "__main__":
    main()
