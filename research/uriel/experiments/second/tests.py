"""Regression tests for independent oracles, exact boundaries and registered predictions."""
from decimal import Decimal as D
from fractions import Fraction as F
from pathlib import Path
from itertools import product
import json
import os
import unittest
from unittest.mock import patch

import arithmetic as ar
import geometry as geo
import finite_certificate as cert
from prime_windows import powers_from_sieve,trial_prime_base

OUT = Path(os.environ.get("URIEL_RESULTS",Path(__file__).resolve().parent/"results"))


def read(name):
    return json.loads((OUT/(name+".json")).read_text())


class PoleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.a = read("analytic")
        cls.p = cls.a["resolution"]

    def test_cancelled_and_recentered(self):
        self.assertTrue(all(abs(D(v))<D("1e-45") for v in self.p["single_pair_cancelled"].values()))
        self.assertEqual(self.p["single_pair_aligned"]["first_one_percent_k"],5)

    def test_exact_tie_and_reversal(self):
        for r in self.p["pairs"]:
            f = F(r["fraction"])
            nearest = [0] if f<F(1,2) else [2] if f>F(1,2) else [0,2]
            self.assertEqual(r["nearest"],nearest)
            self.assertEqual("samples" in r,len(nearest)==1)

    def test_certificates_and_first_crossing(self):
        rows = self.p["pairs"]+[self.p["single_pair_aligned"]]
        for r in rows:
            if len(r["nearest"])!=1:
                continue
            samples = {s["k"]:s for s in r["samples"]}
            k = r["first_one_percent_k"]
            self.assertTrue(all(s["residual_bounds_hold"] for s in samples.values()))
            self.assertGreater(D(samples[k-1]["triangle"]),D(".01"))
            self.assertLessEqual(D(samples[k]["triangle"]),D(".01"))

    def test_quadratic_resolution_prediction(self):
        matched = [r for r in self.p["pairs"] if r["fraction"]=="0" and F(r["h"])<=F(1,8)]
        self.assertEqual(len(matched),2)
        for r in matched:
            self.assertLess(abs(1-D(r["ratio_to_limit"])),D(".02"))

    def test_combined_window(self):
        self.assertEqual(len(self.a["windows"]),36)
        self.assertTrue(all(D(r["margin"])>=-D("1e-45") for r in self.a["windows"]))
        self.assertTrue(all(D(r["left_tail"])>0 and D(r["right_tail"])>0 for r in self.a["windows"]))

    def test_negative_control(self):
        for r in self.a["negative_control"]:
            self.assertEqual(D(r["lhs"]),0)
            self.assertGreaterEqual(D(r["signed_margin"]),0)
            self.assertLess(D(r["omit_real_margin"]),0)

    def test_two_independent_integrals(self):
        self.assertLess(D(self.a["cross_precision_max"]),D("1e-40"))
        self.assertEqual(len(self.a["moment_quadrature"]),2)
        for r in self.a["moment_quadrature"]:
            self.assertLess(D(r["absolute_discrepancy"])+D(r["omitted_envelope"]),D("1e-40"))
        self.assertTrue(all(D(r["mass_quadrature_error"])<D("1e-40") for r in self.a["windows"]))


class ArithmeticTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.a = read("arithmetic")
        cls.rows = cls.a["grid"]

    def test_integer_rounding_by_definition(self):
        for n,d,p in product(range(37),range(1,8),range(1,9)):
            y = ar.ceil_root_ratio(n,d,p)
            self.assertGreaterEqual(d*y**p,n)
            self.assertTrue(y==0 or d*(y-1)**p<n)
        for p in (2,8,16):
            for y in (2,3,19,2**81):
                for shift in (-1,0,1):
                    n = y**p+shift
                    a = ar.even_ceiling(n,p)
                    self.assertEqual(a%2,0)
                    self.assertTrue(a**p>=n>(a-2)**p)

    def test_grid_constructs_ranks_and_cardinalities(self):
        self.assertEqual(len({(r["base"],r["q"],r["j"]) for r in self.rows}),36)
        for r in self.rows:
            self.assertTrue(r["threshold_16"] and r["cyclic_exponent_ge_two"])
            for key in ("ranks","rankval","scale","host_cardinality"):
                self.assertTrue(all(r[key].values()),(key,r["q"],r["base"],r["j"]))

    def test_exact_size_gate_and_budget(self):
        good = [r for r in self.rows if all(r["size_windows"].values())]
        self.assertEqual(len(good),sum(r["L"]**3>=26**8 for r in self.rows))
        self.assertTrue(all(r["budget"]["envelope_holds"] for r in good))
        self.assertTrue(all(r["budget"]["normalizations_equal"] for r in self.rows))

    def test_inadmissible_both_possible_outcomes(self):
        bad = [r for r in self.rows if not all(r["size_windows"].values())]
        self.assertEqual({r["budget"]["envelope_holds"] for r in bad},{True,False})

    def test_t_identity_ablation(self):
        for r in self.rows:
            self.assertTrue(all(r["t_plus_two_ranks"].values()))
            self.assertEqual([k for k,v in r["t_plus_two_rankval"].items() if not v],["identity"])

    def test_fractional_floors(self):
        for label in ("TT","T2"):
            tests = [(r["rounded"][label+"_fractional"],r["rounded"][label+"_floor_pass"]) for r in self.rows]
            self.assertEqual(set(tests),{(True,False),(False,True)})

    def test_invalid_scales_and_archive_recount(self):
        self.assertTrue(all(not all(r["fields"].values()) for r in self.a["scale_controls"]))
        self.assertEqual(self.a["round_one"]["inadmissible_exceed"],4)
        self.assertEqual(self.a["round_one"]["selected_in_both_domains"],1)

    def test_post_registration_cost_ablations(self):
        r, = (r for r in self.rows if "sensitivity" in r)
        self.assertTrue(all(r["size_windows"].values()) and r["budget"]["envelope_holds"])
        for v in r["sensitivity"].values():
            self.assertTrue(v["failed"])
            self.assertFalse(v["budget"]["envelope_holds"])
        a = r["amplified_product"]
        self.assertTrue(a["unit_component_pass"] and a["boundary_pass"])
        self.assertFalse(a["twice_boundary_pass"] or a["unit_product_pass"])


class ExceptionAndSlopeTests(unittest.TestCase):
    def test_congruence_enumerator_against_brute_force(self):
        for p,Z in product((2,3,5,7),range(1,38)):
            weak,strong = geo.moduli(p,Z)
            self.assertTrue(weak<=Z<strong)
            for m in (weak,strong):
                for s in (-4,0,1,Z,Z+2):
                    self.assertEqual(list(geo.near(s,m,Z)),[k for k in range(1,Z+1) if (s-k)%m==0])

    def test_strict_exceptions_and_weak_collisions(self):
        c = read("cohomology")
        self.assertTrue(all(r["strict_max"]<=1 for r in c["prime_ranges"]))
        self.assertTrue(any(r["weak_max"]>1 for r in c["prime_ranges"]))
        self.assertEqual(c["collision"]["weak"],[1,5])

    def test_closed_window_edges(self):
        self.assertTrue(geo.good_interval(F(1),[1,2,17]))
        for e in (3,4,15,16):
            self.assertFalse(geo.good_interval(F(1),[e]))
        with self.assertRaises(ValueError):
            geo.select(1,4,[2,3])

    def test_joint_selector(self):
        cases = read("cohomology")["combined"]
        for r in cases:
            self.assertTrue(r["in_range"] and r["each_good"] and r["union_good"])
            self.assertLessEqual(len(r["union"]),r["R"])
        self.assertTrue(any(not r["naive_good"] for r in cases))

    def test_gram_and_denominator(self):
        for r in read("slopes")["lattices"]:
            self.assertTrue(all(r[k] for k in ("rank_ok","idempotent","symmetric","index_identity","exact_cut")))
            self.assertEqual(r["projector_denominator"],1+r["q"]**2)
            self.assertEqual(F(r["good_gram"]),1+r["q"]**2)
            self.assertFalse(r["omit_denominator_cut_holds"])

    def test_coefficient_sharpness(self):
        r = read("slopes")["boundary"]
        self.assertEqual(F(r["required_constant"]),12)
        for w in r["tests"]:
            self.assertEqual(w["holds"],F(w["constant"])>=12)


class ActualPrimeTests(unittest.TestCase):
    def test_outward_fixed_point_arithmetic(self):
        for a,b in product((F(-1,3),F(-5),F(0),F(2,11),F(7,5)),repeat=2):
            A,B=cert.Interval.of(a),cert.Interval.of(b)
            for v,x in ((A+B,a+b),(A-B,a-b),(A*B,a*b),(A.times(b),a*b)):
                self.assertLessEqual(v.lo,x*cert.S)
                self.assertLessEqual(x*cert.S,v.hi)
        q=F(7,13)
        iv=cert.sqrt_interval(q)
        self.assertLessEqual(iv.lo**2,q*cert.S**2)
        self.assertGreaterEqual(iv.hi**2,q*cert.S**2)

    def test_prime_window_enclosure(self):
        r=read("finite_certificate")
        self.assertLess(r["largest_D_upper_units"],0)
        self.assertGreater(r["lower_witness_D_lower_units"],0)
        self.assertLess(F(r["endpoint_upper"]),F(r["lower"]))
        self.assertLess(F(r["upper"])-F(r["lower"]),F(1,10**9))

    def test_falsified_ceiling_rejected(self):
        with patch.object(cert,"HIGH",F("0.11")):
            with self.assertRaisesRegex(ValueError,"Upper certificate inconclusive"):
                cert.run()

    def test_prime_powers(self):
        self.assertEqual(powers_from_sieve(16),{2:2,3:3,4:2,5:5,7:7,8:2,9:3,11:11,13:13,16:2})
        self.assertEqual(trial_prime_base(6),0)
        self.assertEqual(trial_prime_base(343),7)

    def test_whole_interval_and_missing_terms(self):
        data = read("prime_windows")
        self.assertTrue(data["tables_agree"])
        self.assertLess(D(data["cross_precision_max"]),D("1e-40"))
        self.assertTrue(any(D(r["endpoint_shortfall"])>D("1e-10") for r in data["windows"]))
        for r in data["windows"]:
            self.assertLess(D(r["direct_error"]),D("1e-40"))
            self.assertEqual(r["omit_n4_delta"],r["omit_n4_expected"])
        bump = data["bump"]
        self.assertEqual(bump["max_integer_change"],0)
        self.assertGreater(D(bump["center_perturbed"]),D(bump["unperturbed_window_max"]))


if __name__=="__main__":
    unittest.main(verbosity=2)
