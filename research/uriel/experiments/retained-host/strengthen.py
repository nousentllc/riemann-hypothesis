"""Expose the inverse-scale share bound and carry it through the pinned host supply."""
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "joint-witness"))
from build_original import pinned_source, pinned_tree

BASE = "Development.AutomorphicArithmetic."
FRAMES = BASE + "ThickFrames."
MODULES = (
    (FRAMES + "topsGroup", "StrongGroup", "x ^ (-1 + eps)", "x⁻¹"),
    (FRAMES + "topsFrame", "StrongFrame", "(x ^ (-1 + eps))", "x⁻¹"),
    (FRAMES + "topsBase", "StrongBase", "(B.sc.x ^ (-1 + eps))", "B.sc.x⁻¹"),
    (FRAMES + "topsChoiceH", "StrongChoice", "(s.x ^ (-1 + eps))", "s.x⁻¹"),
    (BASE + "ShortNorms.hostOfFieldOf", "StrongHost", "(s.x ^ (-1 + s.eps))", "s.x⁻¹"),
)


def once(s, old, new):
    if s.count(old) != 1:
        raise ValueError(f"Expected one pinned source fragment: {old!r}")
    return s.replace(old, new)


def generate(archive, tree):
    result = {}
    previous = None
    for original, new, old_radius, new_radius in MODULES:
        path = Path("src", *original.split(".")).with_suffix(".lean")
        s = pinned_source(path, archive, tree).decode()
        short = original.split(".")[-1]
        s = once(s, "." + short + " :", "." + short + "_inv :")
        s = once(s, old_radius, new_radius)
        if previous is None:
            # All the estimates, including the bad-orbit estimate for this T, are in scope.
            ending = """  refine ⟨T, hS1, hS2, fun γ => le_trans (hS3 γ) ?_, hT2⟩
  refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)"""
            s = once(s, ending, "  exact ⟨T, hS1, hS2, hS3, hT2⟩")
        else:
            mod, imported, called = previous
            s = once(s, "import " + mod + "\n", "import " + imported + "\n")
            s = once(s, called + " eps ", called + "_inv eps ")
        full = ("UpperTheory.T3." if new == "StrongHost" else
                "UpperTheory.BernoulliSumsFrobeniusOrbits.") + short + "_inv"
        result[new] = (s + "\n#print axioms " + full + "\n").encode()
        previous = original, new, short
    original = BASE + "ShortNorms.supplyOfAdmOf"
    path = Path("src", *original.split(".")).with_suffix(".lean")
    s = pinned_source(path, archive, tree).decode()
    s = once(s, "UpperTheory.T3.supplyOfAdmOf :", "UpperTheory.T3.supplyOfAdmOf_inv :")
    s = once(s, "(s.x ^ (-1 + s.eps))) →", "s.x⁻¹) →")
    s = once(s, "H _ => EAtH", "H _ => R.toFrame.Shares H.TT s.x⁻¹ ∧ EAtH")
    s = once(s, "hCT, hGood, ?_, ?_⟩", "hCT, hGood, hSh, ?_, ?_⟩")
    s = once(s, "    rw [hs] at hSh ⊢", """    have weak : R.toFrame.Shares H.TT (s.x ^ (-1 + s.eps)) := by
      intro γ
      apply (hSh γ).trans
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith [s.eps_pos])
    rw [hs] at weak ⊢""")
    s = once(s, "hps, hSh, hbd.1", "hps, weak, hbd.1")
    result["StrongSupply"] = (s + "\n#print axioms UpperTheory.T3.supplyOfAdmOf_inv\n").encode()
    return result
