# What changes when more primes ramify?

The conductor-one field $F=\mathbf Q(\zeta_3)$ has class number 1. In its usual cyclotomic tower, the first two cubic steps lead to fields that also have class number 1. We constructed two other cyclic cubic extensions of this **same** $F$. Their class numbers are 36 and 9. The new extensions have the same ramification indices as each other. More than one prime of $F$ ramifies in each. Together they show why the one-ramified-prime hypothesis matters and why ramification indices alone cannot determine an exact class number. [Certified field computations](results/certified_fields.json) · [Ramification intersections](results/ramification_control.json)

## The seven finite fields

Let $D_1,D_2$ be the two cyclic cubic fields of conductor 91, and let $K_i=F D_i$. The index identifies the polynomial in this table and the corresponding entry in the recorded output. The two signs used to enumerate diagonal characters are an unordered pair. Assigning an individual sign to a polynomial is unnecessary for these tests.

| Field | Degree over $\mathbf Q$ | Class group | Class number |
|---|---:|---|---:|
| $\mathbf Q(\zeta_3)$ | 2 | trivial | 1 |
| $\mathbf Q(\zeta_9)$ | 6 | trivial | 1 |
| $\mathbf Q(\zeta_{27})$ | 18 | trivial | 1 |
| $D_1$, polynomial $x^3-x^2-30x-27$ | 3 | $C_3$ | 3 |
| $D_2$, polynomial $x^3-x^2-30x+64$ | 3 | $C_3$ | 3 |
| $K_1$ | 6 | $C_6\times C_6$ | 36 |
| $K_2$ | 6 | $C_3\times C_3$ | 9 |

Here $C_m$ denotes a cyclic group of order $m$. The program selects the cubic subfields of $\mathbf Q(\zeta_{91})$ with field discriminant $91^2$. It then forms each compositum with $F$. Both resulting sextic fields have discriminant $-1{,}851{,}523{,}947$. All seven default, full calls to PARI/GP 2.19.1's `bnfcertify` returned 1. This removes the usual GRH assumption from the computed class-group data. The script and JSON preserve all seven defining polynomials. These are finite arithmetic computations. The Lean deduction for arbitrary cyclotomic layers is a separate check. [GP input](certify_fields.gp) · [Machine-readable results](results/certified_fields.json) · [PARI documentation for bnfcertify](https://pari.math.u-bordeaux.fr/dochtml/ref/General_number_fields.html#bnfcertify)

## Which primes ramify?

Inside $\mathbf Q(\zeta_{273})$, keep the quadratic character at 3 and one cubic character at each of 7 and 13. Their common field $T$ has Galois group $C_2\times C_3\times C_3$ over $\mathbf Q$. Thus $`\mathrm{Gal}(T/F)=C_3\times C_3`$. Each diagonal cubic character on this pair gives one $K_i$. Each coordinate character instead retains the contribution of just one rational prime. We used the coordinate at 7 as a control.

The inertia at a prime $q\mid273$ comes from the $q$-coordinate of the cyclotomic Galois group. Indeed, the prime-to-$q$ cyclotomic part is unramified there, and the ramification index in the full squarefree cyclotomic field is $q-1$, the order of the $q$-factor. The program uses the Chinese remainder theorem to represent the group, checks all $144^2=20{,}736$ products, and intersects each inertia group with the subgroup fixing the indicated intermediate field. In the table the three entries in each tuple correspond to rational primes 3, 7 and 13. Each relative extension in the table has degree 3. [Cyclotomic ramification formula](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean#L402-L425) · [Exact finite group computation](ramification_control.py)

| Middle field $K$ between $F$ and $T$ | Ramification indices in $K/F$ | Ramification indices in $T/K$ |
|---|---|---|
| Either diagonal $K_i$ | $(1,3,3)$ | $(1,1,1)$ |
| Coordinate field at 7 | $(1,3,1)$ | $(1,1,3)$ |

Both 7 and 13 split in $F$ because they are $1\bmod 3$. Thus **four prime ideals of $F$** ramify in each $K_i/F$, over two rational primes. All primes outside 273 are unramified in the full cyclotomic field, and $F$ has no real places. In the diagonal cases $T/K_i$ is therefore an everywhere-unramified cyclic cubic extension. This gives a second explanation of $3\mid h(K_i)$ by the Hilbert class field theorem. For the coordinate field, ramification at 13 prevents this particular extension from giving that conclusion. [Computed intersections](results/ramification_control.json) · [Class-field deduction](ClassAscent.lean)

## What stays fixed under Galois action?

For each $K_i/F$, the program transports the ideal-class generators under each of the two nonidentity automorphisms of order three and enumerates fixed classes in the certified class group. It found **nine fixed classes in both fields**, for either automorphism. In $K_1$, the other 27 classes form nine orbits of size three. In $K_2$ all nine classes are fixed. The two automorphisms generate the same subgroup, so agreement checks the action computation. They supply one fixed-subgroup count per field. [Follow-up prediction](CONTROLS.md) · [Action computation](certify_fields.gp) · [Recorded counts](results/certified_fields.json)

In these two examples the orbit congruence holds, since $36\equiv9\equiv0\pmod3$. The proposed bound that the fixed subgroup order divides the downstairs class number, written $`|\mathrm{Cl}(K_i)^G|\mid h(F)`$, fails because $9\nmid1$. This separates the universal finite-group calculation from the arithmetic hypothesis needed for the one-ramified-prime argument.
