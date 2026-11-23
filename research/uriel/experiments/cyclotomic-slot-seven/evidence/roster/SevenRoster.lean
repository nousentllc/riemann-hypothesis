import FixedRoster
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.SplittingFieldIsoQuadratic
import Mathlib.NumberTheory.NumberField.ClassNumber

open NumberField NumberField.InfinitePlace Formalism.HC UpperTheory.V UpperTheory.V.HV

namespace SevenRoster

/-- The quadratic field used to select the roster has discriminant -7.
Its Minkowski bound is less than two. -/
theorem quadratic_class_one : NumberField.classNumber (Kstar 7) = 1 := by
  obtain ⟨hd,htc,hn,_⟩ := kstar 7 (by decide) (by decide)
  letI := htc
  have hsig := card_add_two_mul_card_eq_rank (Kstar 7)
  have hr : nrRealPlaces (Kstar 7) = 0 := IsTotallyComplex.nrRealPlaces_eq_zero (K := Kstar 7)
  have hc : nrComplexPlaces (Kstar 7) = 1 := by omega
  apply NumberField.classNumber_eq_one_iff.mpr
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [hd,hc,hn]
  norm_num
  nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]

theorem hStar_one : hStar PChar.one = 1 := by
  calc
    hStar PChar.one = NumberField.classNumber (Kstar 7) :=
      congrArg (fun p : ℕ => NumberField.classNumber (Kstar p)) FixedRoster.prime_k
    _ = 1 := quadratic_class_one

theorem principalRoster : Bchi PChar.one = {3,7} :=
  FixedRoster.roster_of_class_one hStar_one

end SevenRoster
#print axioms SevenRoster.quadratic_class_one
#print axioms SevenRoster.hStar_one
#print axioms SevenRoster.principalRoster
