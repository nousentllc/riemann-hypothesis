"""Cross-check the finite construction and its failure controls."""
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from itertools import combinations
import math
import unittest

import finite_probe as probe


def power_by_squaring(base, exponent, modulus):
    result = 1
    for bit in bin(exponent)[2:]:
        result = result * result % modulus
        if bit == "1":
            result = result * base % modulus
    return result


class JointWitnessTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = probe.run_probe()

    def test_independent_modular_order_certificate(self):
        c = self.report["certificate"]
        p = c["F_exponent"]
        factor = 2**p-1
        n = int(c["d"])
        self.assertTrue(all(p%j for j in range(2,p)))
        # Reduction by repeated folding modulo 2^p-1 gives an independent LL check.
        s = 4
        for _ in range(p-2):
            s = s*s-2
            while s > factor:
                s = (s >> p) + (s & factor)
            s %= factor
        self.assertEqual(s,0)
        self.assertEqual(n-1,2*c["k"]*factor)
        self.assertGreater(factor,math.isqrt(n))
        self.assertEqual(power_by_squaring(c["pocklington_base"],n-1,n),1)
        self.assertEqual(math.gcd(power_by_squaring(c["pocklington_base"],2*c["k"],n)-1,n),1)

    def test_reject_corrupted_prime_certificate(self):
        c = self.report["certificate"]
        d = int(c["d"])
        self.assertFalse(probe.certified(d,1279,1))
        self.assertFalse(probe.certified(d+2,1279,2))
        self.assertFalse(probe.certified(d,1277,2))
        self.assertFalse(probe.mersenne_prime(11))

    def test_classical_row_by_separate_decimal_evaluation(self):
        r = self.report
        q, d = r["certificate"]["q"], int(r["certificate"]["d"])
        with localcontext() as ctx:
            ctx.prec = 90
            T = Decimal(2)**48
            z = T**(1/Decimal(320))
            h = z*T.ln()**2
            self.assertTrue(z/2 < Decimal(q).ln() <= z)
            self.assertTrue(h/2 < Decimal(d).ln() <= h)
            self.assertTrue(Decimal(q*d*(2**308)).ln() <= 2*h)
            self.assertTrue(1 < z < 2)
            self.assertGreater(Decimal(q*d).ln(),Decimal(2)**(Decimal(3)/16))
        self.assertEqual((q%8,d%16,d%q),(3,7,q-1))
        self.assertIn((-d)%q,{x*x%q for x in range(q)})
        self.assertTrue(r["original_q"]["row_all"])
        self.assertTrue(r["prime_pair_conductor_one"])

    def test_mutated_q_still_passes_prime_pair_but_breaks_two_clauses(self):
        self.assertTrue(self.report["mutant_prime_pair_conductor_one"])
        clauses = self.report["mutant_q11"]["clauses"]
        self.assertEqual({k for k,v in clauses.items() if not v},{"q_upper","pair_symbol_one"})

    def test_selector_against_exact_forbidden_intervals(self):
        grid = [Q(i,2) for i in range(9)]
        for B in (1,2,4):
            for count in range(4):
                for points in combinations(grid,count):
                    y, _ = probe.select(4,B,count,points)
                    self.assertLessEqual(Q(4,2**(count+2)*B**count),y)
                    self.assertLessEqual(2*y,4)
                    self.assertIsNone(probe.bad_at(y,B,points))
        self.assertEqual(probe.bad_at(2,4,[4]),(4,4))
        self.assertIsNone(probe.bad_at(4,4,[1]))
        with self.assertRaises(ValueError):
            probe.select(4,2,0,{1})

    def test_same_scale_and_strict_domain_failure(self):
        r = self.report
        s = r["selected_scale"]
        c = r["coordinates"]
        self.assertEqual(c["log2_X"],48*c["J"])
        self.assertEqual((c["log2_window_start"],c["log2_x"]),(96,144))
        self.assertEqual(c["log2_x"]*17,8*s["e"])
        self.assertEqual(s["QS_log2"],s["e"]+2)
        self.assertEqual(s["t_log2"],401*c["log2_x"])
        self.assertTrue(all(s[key] for key in ("PageN","PairWin","inside_common_window")))
        self.assertTrue(r["selector"]["whole_union_good"])
        w = r["selector"]["omitted_odd_window_log2"]
        self.assertEqual(r["selector"]["violation_normalized_exception_and_point"],[w,w])
        gates = r["cohomological_prerequisites"]
        self.assertGreaterEqual(gates["log_qd_lower_integer"],896)
        self.assertTrue(all(gates[k] is False for k in ("log_size_pass","q_gt_2XpowCt_plus_1","d_gt_2XpowCt_plus_1")))

    def test_scaled_field_exponent_and_height(self):
        t = self.report["post_hoc_winPairs_transport"]
        self.assertEqual((t["e_x_prime"],t["e_x"]),(306,307))
        self.assertTrue(all(t[k] for k in ("pre_pair_thresholds","final_scale_in_range",
            "evaluation_in_cohomology_window","scaled_page_at_e_x_prime","floor_transport_by_monotonicity")))
        self.assertFalse(t["scaled_page_at_e_x"])
        b = t["bad_k_log2_half"]
        self.assertTrue(b["cubic_window_inclusion"])
        self.assertEqual((b["requested_t_log2"],b["available_t_log2"]),(38600,38496))
        self.assertFalse(b["floor_transport"])
        self.assertFalse(t["bad_k_log2_33"]["cubic_window_inclusion"])


if __name__ == "__main__":
    unittest.main()
