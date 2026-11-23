"""Exact odd-character norm for odd prime-power conductors. Python standard library."""
import argparse
from hashlib import sha256
import json
from math import gcd, isqrt, prod

def prime(n):
    if n < 2 or n % 2 == 0:
        return n == 2
    return all(n % x for x in range(3, isqrt(n) + 1, 2))

def factors(n):
    answer = []
    k = 2
    while k * k <= n:
        if n % k == 0:
            answer.append(k)
            while n % k == 0:
                n //= k
        k += 1
    if n > 1:
        answer.append(n)
    return answer

def generator(modulus, order):
    divisors = factors(order)
    for g in range(1, modulus):
        if gcd(g, modulus) == 1 and pow(g, order, modulus) == 1:
            if all(pow(g, order // r, modulus) != 1 for r in divisors):
                return g
    raise ValueError("Noncyclic unit group")

def exact_root(order, q):
    for a in range(2, q):
        root = pow(a, (q - 1) // order, q)
        if all(pow(root, order // r, q) != 1 for r in factors(order)):
            return root
    raise ValueError("No primitive root")

def transform(coeff, root, q):
    """Evaluate at all powers of the supplied root by a mixed-radix positive DFT."""
    n = len(coeff)
    if n == 1:
        return coeff
    radix = factors(n)[0]
    inner = n // radix
    parts = [transform(coeff[r::radix], pow(root, radix, q), q) for r in range(radix)]
    result = []
    twiddle = 1
    for j in range(n):
        value = 0
        for r in reversed(range(radix)):
            value = (value * twiddle + parts[r][j % inner]) % q
        result.append(value)
        twiddle = twiddle * root % q
    return result

def modular_norm(coeff, q):
    d = len(coeff)
    root = exact_root(2*d, q)
    assert pow(root, d, q) == q - 1
    twists = [c * pow(root, k, q) % q for k, c in enumerate(coeff)]
    values = transform(twists, root*root % q, q)
    product = 1
    for v in values:
        product = product * v % q
    return product

def resultant(coeff):
    d = len(coeff)
    bound = sum(map(abs, coeff))**d
    mod, residue = 1, 0
    # The strict bound makes Chinese remaindering an integer proof, not a fingerprint.
    step = 2*d
    q = ((100_000_000+step-1)//step)*step + 1
    used = []
    while mod <= 2*bound:
        if prime(q):
            observed = modular_norm(coeff, q)
            residue += mod * (((observed-residue) * pow(mod, -1, q)) % q)
            mod *= q
            used.append((q, observed))
        q += step
    signed = residue if residue*2 < mod else residue-mod
    assert abs(signed) <= bound
    return signed, dict(moduli=len(used), modulus_bits=mod.bit_length(), norm_bound_bits=bound.bit_length(),
                       moduli_and_residues_sha256=sha256(json.dumps(used, separators=(',', ':')).encode()).hexdigest())

def direct_det(coeff):
    """Bareiss elimination on the integer multiplication matrix in Z[T]/(T^d+1)."""
    d = len(coeff)
    mat = [[coeff[i-j] if i >= j else -coeff[i-j+d] for j in range(d)] for i in range(d)]
    last, sign = 1, 1
    for k in range(d-1):
        if mat[k][k] == 0:
            pivot = next((i for i in range(k+1, d) if mat[i][k] != 0), None)
            if pivot is None:
                return 0
            mat[k], mat[pivot] = mat[pivot], mat[k]
            sign = -sign
        pivot = mat[k][k]
        for i in range(k+1, d):
            for j in range(k+1, d):
                n = mat[i][j]*pivot - mat[i][k]*mat[k][j]
                mat[i][j], rem = divmod(n, last)
                if rem:
                    raise ArithmeticError("Nonexact Bareiss division")
        last = pivot
    return sign*mat[-1][-1]

def coefficients(m, g, d):
    reps = [pow(g, j, m) for j in range(d)]
    assert all(m-r == pow(g, j+d, m) for j,r in enumerate(reps))
    return [m-2*r for r in reps]

def row(p, a):
    assert prime(p) and p > 2 and a >= 1
    m = p**a
    d = (m-m//p)//2
    g = generator(m, 2*d)
    coeff = coefficients(m, g, d)
    norm, certificate = resultant(coeff)
    h, rem = divmod(norm, (2*m)**(d-1))
    if rem or h <= 0:
        raise ArithmeticError("Normalization of relative class number failed")
    alt = pow(g, -1, m)
    other_coeff = coefficients(m, alt, d)
    if m <= 343:
        assert resultant(other_coeff)[0] == norm
    if m <= 343:
        assert direct_det(other_coeff) == norm
    return dict(prime=p, power=a, conductor=m, degree=2*d, odd_characters=d, generator=g,
                inverse_generator=alt, relative_class_number=str(h), residue_at_tower_prime=h%p,
                direct_determinant_and_alternate_generator=(m<=343), certificate=certificate)

def run(extended=False):
    panel = [(3,1),(3,2),(3,3),(7,1),(7,2),(7,3),(23,1),(37,1)]
    if extended:
        panel += [(7,4)]
    return dict(method="odd characters; certified integer norm by split-prime DFT and CRT",
                primary_conductors=[3,9,27,7,49,343,23,37],rows=[row(p,a) for p,a in panel])

if __name__ == "__main__":
    cmd = argparse.ArgumentParser(description=__doc__)
    cmd.add_argument("--extended", action="store_true", help="include the secondary conductor 2401")
    print(json.dumps(run(cmd.parse_args().extended), indent=2))
