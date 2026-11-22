"""Regression tests of operational predictions, not proofs of the source theorems."""
from fractions import Fraction as F
from functools import cache
import math
import unittest

from mechanisms import analytic,arithmetic,cohomology,covolume,select_window,whole_window
from source_audit import audit,contains_token,declarations,get_decl,mask_comments


@cache
def results():
    return dict(analytic=analytic(),arithmetic=arithmetic(),cohomology=cohomology(),covolume=covolume(),source=audit())


class AnalyticTests(unittest.TestCase):
    def test_residue_sign_control(self):
        r=results()['analytic']['windows']
        self.assertGreater(r[-1]['positive_log_ratio'],0)
        self.assertTrue(all(x['negative_mass']==0 and x['negative_residue']<0 for x in r))

    def test_missing_late_intervals(self):
        r=results()['analytic']['windows']
        self.assertIsNone(r[0]['delayed_log_ratio'])
        self.assertIsNone(r[2]['delayed_log_ratio'])
        self.assertGreater(r[-1]['delayed_log_ratio'],0)

    def test_mesh_misses_spike(self):
        r=results()['analytic']['spike']
        self.assertLess(r['sampled_mass'],r['allowed_mass'])
        self.assertGreater(r['full_weighted_mass'],r['allowed_mass'])

    def test_source_tail_constants(self):
        rows=results()['analytic']['tails']
        self.assertEqual(len(rows),9)
        self.assertTrue(all(x['passes'] and math.isfinite(x['log_scaled_tail']) for x in rows))

    def test_low_sigma_is_not_uniform_control(self):
        r=results()['analytic']['low_sigma']
        self.assertGreater(r[-1]['log_scaled_tail']-r[0]['log_scaled_tail'],100)

    def test_high_derivatives_by_quadrature(self):
        rows=results()['analytic']['quadrature']
        self.assertEqual(len(rows),24)
        self.assertLess(max(x['relative_error'] for x in rows),1e-10)

    def test_nearest_pole_separation_and_tie(self):
        r=results()['analytic']['growth']
        self.assertGreater([x for x in r if x['d']==2.25][-1]['log_pole_to_allowance'],0)
        self.assertTrue(all(x['log_pole_to_allowance']<=1e-12 for x in r if x['d']==2.4))


class ArithmeticTests(unittest.TestCase):
    def test_independent_bracket_normalization(self):
        self.assertLess(results()['arithmetic']['identity_max_relative_error'],1e-10)

    def test_admissible_budgets(self):
        r=results()['arithmetic']
        self.assertEqual(len(r['sampled']),900)
        self.assertTrue(all(x['admissible'] and x['bound_passes'] for x in r['sampled']))
        self.assertTrue(all(x['bound_passes'] for x in r['selected'] if x['admissible']))

    def test_finite_threshold_not_silently_ignored(self):
        self.assertTrue(any(not x['constraints']['absorb_constant'] for x in results()['arithmetic']['selected']))

    def test_constraint_ablations_rejected(self):
        rows=results()['arithmetic']['ablations']
        self.assertTrue(all(not x['admissible'] for x in rows))
        self.assertTrue(all(not x['bound_passes'] for x in rows))

    def test_exact_weak_error_contradiction(self):
        r=results()['arithmetic']['weak_counterexample']
        self.assertGreater(int(r['lhs']),int(r['rhs']))
        self.assertGreater(r['ratio'],1e19)


class WindowTests(unittest.TestCase):
    def test_whole_interval_exhaustive_and_random(self):
        r=results()['cohomology']
        # B=1 merges cut=U/(2B) with U/2: 163+256+256 grid subsets, plus 300 seeded.
        self.assertEqual(r['cases'],163+256+256+300)
        self.assertEqual(r['failures'],[])

    def test_adversarial_moving_exceptions(self):
        self.assertTrue(all(x['selected_passes'] and not x['naive_passes'] for x in results()['cohomology']['moving']))

    def test_cap_and_omitted_exception(self):
        r=results()['cohomology']
        self.assertTrue(r['understated_cap_rejected'])
        self.assertFalse(r['omitted_exception_passes'])
        self.assertTrue(r['endpoint_failure_detected'])

    def test_boundary_and_nonpositive_indices(self):
        self.assertEqual(select_window(1,2,64,{16}),F(32))
        self.assertTrue(whole_window(F(2),F(32),{F(-1),F(0),F(16)}))
        self.assertFalse(whole_window(F(2),F(32),{F(64)}))
        with self.assertRaises(ValueError):select_window(1,F(1,2),64,{1})


class CovolumeTests(unittest.TestCase):
    def test_exact_numeric_hypotheses(self):
        r=results()['covolume']
        self.assertEqual(r['numeric_failures'],[])
        self.assertGreaterEqual(r['min_numeric_slack'],0)

    def test_one_hypothesis_ablations(self):
        for r in results()['covolume']['ablations']:
            self.assertEqual(r['failed_hypotheses'],[r['label']])
            self.assertFalse(r['conclusion_holds'])

    def test_lattice_projection_denominators(self):
        for r in results()['covolume']['lattices']:
            self.assertLess(r['idempotence_error'],1e-10)
            self.assertLess(r['orthogonality_error'],1e-10)
            self.assertLess(r['integrality_error'],1e-9)
            self.assertGreaterEqual(r['cut_rhs'],0)
            self.assertLess(r['cut_without_denominator_rhs'],0)
            self.assertAlmostEqual(r['retained_intersection_covolume']*r['projected_image_covolume'],1)

    def test_nonorthogonal_idempotent(self):
        r=results()['covolume']['nonorthogonal']
        self.assertEqual(r['idempotence_error'],0)
        self.assertLess(r['pythagorean_residual'],-1)

    def test_eventual_absorption(self):
        r=results()['covolume']['absorption']
        for ez in [.1,1.]:
            rows=[x for x in r if x['ez']==ez]
            self.assertFalse(rows[0]['underflow_safe_pass'])
            self.assertTrue(rows[-1]['underflow_safe_pass'])


class SourceTests(unittest.TestCase):
    def test_pin_and_source_guards(self):
        r=results()['source']
        self.assertEqual(r['prior_trace_files'],55)
        self.assertEqual(r['failures'],[])
        self.assertTrue(all(x['mutation_detected'] for x in r['guards']))

    def test_comment_only_dependencies_excluded(self):
        self.assertTrue(results()['source']['comment_bait_ignored'])
        txt='theorem a : True := by\n /- /- deep -/ bogus -/\n -- bogus\n trivial\n'
        self.assertFalse(contains_token(get_decl(txt,'a')['body'],'bogus'))
        self.assertEqual(len(mask_comments(txt)),len(txt))

    def test_imports_are_not_theorem_edges(self):
        txt='import Bogus\ntheorem a : True := by trivial\n'
        self.assertFalse(contains_token(get_decl(txt,'a')['body'],'Bogus'))
        self.assertTrue(all(not e['theorem_dependency'] for e in results()['source']['imports']))

    def test_no_kernel_claim(self):
        r=results()['source']
        self.assertFalse(r['full_dependency_closure'])
        self.assertFalse(r['axiom_inventory_checked'])
        self.assertFalse(r['verification']['kernel_replay_attempted'])


if __name__=='__main__':
    unittest.main(verbosity=2)
