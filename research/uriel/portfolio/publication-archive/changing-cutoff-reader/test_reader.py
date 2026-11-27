"""Checks for source identity, the supervision split, and decision logic."""
from collections import Counter
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from unittest import TestCase, main
from unittest.mock import patch

import run


class ReaderTests(TestCase):
    def test_archive_agrees_with_all_terminal_weights(self):
        path = run.HERE.parent / "slot3-witness-memory" / "benchmark.py"
        spec = spec_from_file_location("slot3_benchmark", path)
        reference = module_from_spec(spec)
        spec.loader.exec_module(reference)
        sets, _ = reference.read_reference(run.HERE.parents[1] / "riemann-experiments")
        self.assertEqual(set(sets), set(range(81)))
        for s, expected in sets.items():
            actual = {e for e in range(1,65) if run.valuation_truth(s,64,e) == run.YES}
            self.assertEqual(actual, expected)
            self.assertEqual(run.encode(s,"terminal_list"), next(iter(expected),0))

    def test_fit_receives_only_training_cuts(self):
        observed = []
        def tiny_cells(channel, cutoffs):
            observed.append(tuple(cutoffs))
            yield (1,2,1,0,4), run.YES, 0, 1
        with patch.object(run,"cells",tiny_cells):
            fitted = run.fit("residue")
        self.assertEqual(observed,[run.TRAIN])
        self.assertFalse(set(run.TRAIN) & set(run.HOLDOUT))
        self.assertEqual(set(run.TRAIN) | set(run.HOLDOUT), set(range(1,65)))
        self.assertTrue(all(run.predict(tree,(1,2,1,0,4)) == run.YES for tree in fitted.values()))

    def test_two_centers_have_identical_visible_terminal_features(self):
        for z in (26,64):
            first = run.features(run.encode(0,"terminal_list"),z,11)
            second = run.features(run.encode(65,"terminal_list"),z,11)
            self.assertEqual(first,second)
            self.assertNotEqual(run.encode(0,"residue"),run.encode(65,"residue"))
        self.assertEqual([run.modular_truth(s,26,11) for s in (0,65)],[run.NO,run.YES])
        self.assertEqual([run.modular_truth(s,64,11) for s in (0,65)],[run.NO,run.NO])

    def test_tree_selects_split_and_handles_tie(self):
        rows = [((1,), (0,3,0)), ((2,), (0,1,0)), ((5,), (0,0,4))]
        tree = run.grow(rows,list(range(len(rows))),1)
        self.assertEqual(tree.threshold,2)
        self.assertEqual(run.predict(tree,(1,)),run.NO)
        self.assertEqual(run.predict(tree,(5,)),run.YES)
        leaf = run.grow([((1,), (1,1,0))],[0],1)
        self.assertEqual(leaf.label,run.ABSTAIN)

    def test_unlicensed_accidental_truth_is_counted_separately(self):
        x=Counter()
        run.accumulate(x,run.ABSTAIN,run.NO,16,1)
        self.assertEqual(x["definite_on_ambiguous"],17)
        self.assertEqual(x["truth_correct"],16)
        self.assertEqual(x["licensed_no"],0)
        self.assertEqual(x["accidentally_true_on_ambiguous"],16)
        self.assertEqual(x["wrong_on_determinate"],0)

    def test_independent_oracle_agrees_on_training_and_holdout(self):
        for s in range(81):
            for z in range(1,65):
                for e in range(1,z+1):
                    self.assertEqual(run.valuation_truth(s,z,e),run.modular_truth(s,z,e))


if __name__=="__main__":
    main()
