import ReadableCapacity
import RecoveryCriteria

open New Formalism.HC Finset Classical
open scoped BigOperators
set_option exponentiation.threshold 1200

namespace SelectedPlace
noncomputable section

/-- The three inequalities below are supplied by the literal original Host and Ranks.
    The native proof checks this transfer in OriginalCapacity.lean. -/
theorem no_actual_injection (φ : Frame) (hφ : Fintype.card φ.A ≤ 22) :
    ¬ ∃ f : FixedDatum.controlDatum.bPlaces → φ.Psi, Function.Injective f := by
  classical
  rintro ⟨f, hf⟩
  have hi := Fintype.card_le_of_injective f hf
  have hs := Fintype.card_congr (FixedDatum.signedIndices φ)
  rw [Fintype.card_prod, Fintype.card_units_int] at hs
  rw [Fintype.card_coe, hs] at hi
  have hl := actual_selected.2.1
  have hbig : 44 < 2 ^ 1071 := by decide
  exact (not_lt_of_ge (hi.trans (Nat.mul_le_mul_left 2 hφ))) (hbig.trans_le hl)

/-- Field equality fails once the native bound on the old index is supplied. -/
theorem no_actual_field_iso {φ : Frame} (H : HostAx φ) (hφ : Fintype.card φ.A ≤ 22) :
    ¬ Nonempty (H.E ≃ₐ[ℚ] FixedDatum.controlDatum.E) := by
  rintro ⟨e⟩
  have htotal := FixedDatum.place_count FixedDatum.controlDatum H e
  have hsize := (Finset.card_le_univ FixedDatum.controlDatum.bPlaces).trans_eq htotal
  have hbig : 44 < 2 ^ 1071 := by decide
  exact (not_lt_of_ge (hsize.trans (Nat.mul_le_mul_left 2 hφ)))
    (hbig.trans_le actual_selected.2.1)

/-- If two finite sets have different cardinalities, their counts cannot agree
    across every class of a common partition, for any choices of the class maps. -/
theorem raw_counts_differ {X Y C : Type*} [Fintype C] [DecidableEq C]
    (S : Finset X) (T : Finset Y) (f : X → C) (g : Y → C) (hlt : T.card < S.card) :
    ∃ c : C, (T.filter (fun y => g y = c)).card < (S.filter (fun x => f x = c)).card := by
  classical
  by_contra! h
  have hs : S.card = ∑ c : C, (S.filter (fun x => f x = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have ht : T.card = ∑ c : C, (T.filter (fun y => g y = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have hle := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset C)) => h c)
  rw [← hs, ← ht] at hle
  exact (not_le_of_gt hlt) hle

/-- This counts the actual readable places. The class map is arbitrary.
    In particular one may choose the class of the unsigned projection of a
    proposed signed map into the old quotient by the cyclic subgroup. -/
theorem some_coset_loses_places (φ : Frame) (hφ : Fintype.card φ.A ≤ 22)
    (TT : Finset φ.A) (f : FixedDatum.controlDatum.Φ → φ.A ⧸ φ.A0) :
    ∃ c : φ.A ⧸ φ.A0,
      (TT.filter (fun t => QuotientAddGroup.mk t = c)).card <
        (FixedDatum.controlDatum.bPlaces.filter (fun v => f v = c)).card := by
  classical
  have ht : TT.card ≤ 22 := (Finset.card_le_univ _).trans hφ
  have hbig : 22 < 2 ^ 1071 := by decide
  exact raw_counts_differ _ _ f QuotientAddGroup.mk
    ((lt_of_le_of_lt ht hbig).trans_le actual_selected.2.1)

end
end SelectedPlace
#print axioms SelectedPlace.no_actual_injection
#print axioms SelectedPlace.some_coset_loses_places
#print axioms SelectedPlace.no_actual_field_iso
