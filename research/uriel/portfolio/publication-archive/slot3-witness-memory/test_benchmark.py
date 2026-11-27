"""Independent expected counts, boundary, label-corruption and provenance controls."""
from pathlib import Path
import unittest

from benchmark import bucket_decisions, experiment, read_reference, residue_trials, strict_scale, valuation_labels


class WitnessRecoveryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        repo = Path(__file__).resolve().parents[2] / "riemann-experiments"
        cls.result = experiment(repo)
        cls.labels = read_reference(repo)[0]

    def test_reference_and_three_valued_counts(self):
        for k, row in enumerate(self.result["partial_residue_trials"]):
            counts = row["counts"]
            ambiguous = 64 * (81 // 3**k) if k < 4 else 0
            self.assertEqual(counts["withheld_positive"] + counts["withheld_negative"], ambiguous)
            self.assertEqual(counts["true_positive"], 0 if k < 4 else 64)
            self.assertEqual(counts["true_negative"], 5184 - ambiguous - counts["true_positive"])
            self.assertEqual(row["coverage"]["denominator"], 5184)
            self.assertEqual(row["positive_recall_all"]["denominator"], 64)
            self.assertEqual(row["negative_specificity_all"]["denominator"], 5120)
        self.assertIsNone(self.result["partial_residue_trials"][0]["accuracy_on_answered"]["value"])
        self.assertEqual(self.result["always_no_comparator"]["counts"]["false_negative"], 64)

    def test_equal_cardinality_swap_and_unbinding(self):
        a, b = self.labels[1], self.labels[2]
        self.assertEqual(len(a), len(b))
        anonymous_rows = [(37, len(a), a), (54, len(b), b)]
        readout = bucket_decisions(anonymous_rows, 64)
        self.assertEqual(readout[(1,1)], "unknown")
        self.assertEqual(readout[(1,2)], "unknown")
        self.assertEqual(readout[(1,3)], "no")
        bound = bucket_decisions([(37, "first", a), (54, "second", b)], 64)
        self.assertEqual((bound["first",1], bound["second",1]), ("yes","no"))

    def test_tag_and_collision(self):
        tag = self.result["tag_bounds"]
        self.assertEqual(tag["mutually_conflicting_profile_pairs"], 65 * 64 // 2)
        self.assertEqual(tag["arbitrary_later_query_symbols"], 65)
        self.assertEqual(tag["arbitrary_later_query_bits"], 7)
        self.assertEqual(tag["six_bit_collision_at_cutoff64"]["distinguishing_weight"], 64)
        self.assertEqual(tag["fixed_weight_bits"], 1)
        self.assertEqual(self.result["controls"]["equal_singleton_cardinality_swaps"], 64 * 63 // 2)
        self.assertEqual(self.result["controls"]["permutation_invariance_decisions"], 5 * 81 * 64)

    def test_tampering_and_strict_boundary(self):
        labels = self.labels.copy()
        labels[1] = frozenset({1,28,55})
        with self.assertRaisesRegex(ValueError, "disagree"):
            residue_trials(labels, 64)
        labels = self.labels.copy()
        labels[1], labels[2] = labels[2], labels[1]
        with self.assertRaisesRegex(ValueError, "disagree"):
            residue_trials(labels, 64)

    def test_power_boundaries(self):
        targets = {26:27,27:81,28:81,80:81,81:243,82:243}
        self.assertEqual({r["cutoff"]:r["strict_modulus"] for r in self.result["held_out_inputs"]},targets)
        for z, full in targets.items():
            self.assertEqual(strict_scale(z)[1], full)
            self.assertEqual(valuation_labels(z)[0], frozenset())
            self.assertEqual(valuation_labels(z)[z], frozenset({z}))


if __name__ == "__main__":
    unittest.main()
