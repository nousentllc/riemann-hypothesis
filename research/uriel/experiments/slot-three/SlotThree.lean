import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Exc
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Lean.Util.CollectAxioms

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V
open UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

namespace SlotThree

/-- An upper-bound exception set can be enlarged, at a cost of at most one in the cap. -/
theorem firstBound_insert {l R c Z : ℕ} [Fact l.Prime] {L : Type} [Field L]
    {E : Finset ℕ} (h : FirstBound l R c L Z E) (a : ℕ) :
    FirstBound l (R + 1) c L Z (insert a E) := by
  refine ⟨(Finset.card_insert_le a E).trans (Nat.add_le_add_right h.1 1), ?_⟩
  intro e hpos hZ hnot m F _ _ _ hF
  have hold := h.2 e hpos hZ (fun he => hnot (Finset.mem_insert_of_mem he)) m F hF
  have hj : jZero l R ≤ jZero l (R + 1) :=
    Nat.add_le_add_right (Nat.log_mono_right (Nat.le_succ R)) 3
  apply hold.trans
  exact_mod_cast Nat.mul_le_mul (Nat.le_succ R)
    (Nat.add_le_add_right (Nat.add_le_add_right (max_le_max_left m hj) c) (Nat.log l Z))

/-- Apply the original `exc` result before naming an integer in a looser witness. -/
theorem can_mark_after_exc {l R : ℕ} [Fact l.Prime] {L : Type} [Field L]
    (h : ABound l R L) (a : ℕ) :
    ∃ c : ℕ, (∃ ζ : L, IsPrimitiveRoot ζ (l ^ c)) ∧ ∀ Z : ℕ,
      ∃ E : Finset ℕ, a ∈ E ∧ FirstBound l (R + 1) c L Z E := by
  obtain ⟨c, hroot, pick⟩ := exc l R L h
  refine ⟨c, hroot, fun Z => ?_⟩
  obtain ⟨E, hb⟩ := pick Z
  exact ⟨insert a E, Finset.mem_insert_self _ _, firstBound_insert hb a⟩

/-- Re-express the arithmetic clause of an original center witness with its parameters. -/
def AwayBound (l R : ℕ) [Fact l.Prime] (L : Type) [Field L]
    (K : Type) [NormedField K] (c r : ℕ) (s : Fin r → K) : Prop :=
  ∀ e : ℕ, 1 ≤ e → ∀ (m : ℕ) (F : Type) [Field F] [NumberField F] [Algebra L F],
    IsLayer l m L F → ∀ B : ℕ, (∀ i, (l : ℝ) ^ (-(B : ℤ)) ≤ ‖s i - (e : K)‖) →
      shaInv F l e ≤ ((r * (max m (jZero l R) + c + B) : ℕ) : ℕ∞)

/-- At fixed cap, an unused center slot accepts any nominated center. -/
theorem awayBound_cons {l R : ℕ} [Fact l.Prime] {L : Type} [Field L]
    {K : Type} [NormedField K] {c r : ℕ} {s : Fin r → K}
    (h : AwayBound l R L K c r s) (a : K) :
    AwayBound l R L K c (r + 1) (Fin.cons a s) := by
  intro e he m F _ _ _ hF B hf
  have hOld := h e he m F hF B (fun i => by simpa using hf i.succ)
  exact hOld.trans (by exact_mod_cast Nat.mul_le_mul_right _ (Nat.le_succ r))

/-- Record a center along with every clause of the original ABound. -/
def HasNamedCenter (l R : ℕ) [Fact l.Prime] (L : Type) [Field L] (a : ℕ) : Prop :=
  (∃ (K : Type) (_ : NormedField K) (_ : NormedAlgebra ℚ_[l] K) (_ : IsUltrametricDist K)
    (c r : ℕ) (s : Fin r → K), r ≤ R ∧ (∃ ζ : L, IsPrimitiveRoot ζ (l ^ c)) ∧
    AwayBound l R L K c r s ∧ ∃ i, s i = (a : K)) ∧ SecondBound l R L

theorem forget_named {l R : ℕ} [Fact l.Prime] {L : Type} [Field L] {a : ℕ}
    (h : HasNamedCenter l R L a) : ABound l R L := by
  obtain ⟨⟨K, hK, halg, hU, c, r, s, hcap, hroot, hfar, _⟩, h2⟩ := h
  exact ⟨⟨K, hK, halg, hU, c, r, s, hcap, hroot, hfar⟩, h2⟩

/-- Retain the old away-from-centers bound and use the second bound at the new tower level. -/
theorem name_with_second {l R S : ℕ} [Fact l.Prime] {L : Type} [Field L]
    (h : ABound l R L) (room : R < S) (second : SecondBound l S L) (a : ℕ) :
    HasNamedCenter l S L a := by
  obtain ⟨⟨K, hK, alg, hU, c, r, s, hcap, hroot, hfar⟩, _⟩ := h
  refine ⟨⟨K, hK, alg, hU, c, r + 1, Fin.cons (a : K) s, by omega, hroot, ?_,
    ⟨0, by simp⟩⟩, second⟩
  apply awayBound_cons
  intro e he m F _ _ _ hF B hf
  have hj : jZero l R ≤ jZero l S := Nat.add_le_add_right (Nat.log_mono_right room.le) 3
  apply (hfar e he m F hF B hf).trans
  exact_mod_cast Nat.mul_le_mul_left r (Nat.add_le_add_right
    (Nat.add_le_add_right (max_le_max_left m hj) c) B)

theorem tower_succ {l R : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L]
    (tower : Tower.IsTower l L R) : Tower.IsTower l L (R + 1) := by
  obtain ⟨π, covers⟩ := tower.gen
  let drop : (Fin (R+1) → ℤ_[l]) →ₗ[ℤ_[l]] (Fin R → ℤ_[l]) :=
    { toFun := fun f i => f i.succ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  refine ⟨tower.complex, tower.mu, by omega, π ∘ₗ drop, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := covers y
  exact ⟨Fin.cons 0 x, by simpa [drop, Fin.cons_succ] using hx⟩

theorem tower_can_name {l R : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L]
    (tower : Tower.IsTower l L R)
    (supply : ∀ S, Tower.IsTower l L S → ABound l S L) (a : ℕ) :
    HasNamedCenter l (R+1) L a :=
  name_with_second (supply R tower) (Nat.lt_succ_self R) (supply (R+1) (tower_succ tower)).2 a

theorem near_named {K : Type} [NormedField K] {s : K} {a : ℕ}
    (h : s = (a : K)) : ‖s - (a : K)‖ < (3 : ℝ) ^ (-(Nat.log 3 64 : ℤ)) := by
  rw [h, sub_self, norm_zero]
  positivity

/-- Use the source's genuine strict-neighborhood filter on a witness with a named center. -/
theorem named_filter {R : ℕ} {L : Type} [Field L] {a : ℕ}
    (h : HasNamedCenter 3 R L a) (ha : 1 ≤ a) (hZ : a ≤ 64) :
    ∃ c : ℕ, (∃ ζ : L, IsPrimitiveRoot ζ (3 ^ c)) ∧
      ∃ E : Finset ℕ, a ∈ E ∧ FirstBound 3 R c L 64 E := by
  classical
  obtain ⟨⟨K, _, _, _, c, r, s, hcap, hroot, hfar, i, hi⟩, _⟩ := h
  let near := fun k : Fin r => (Finset.Icc 1 64 : Finset ℕ).filter
    (fun e : ℕ => ‖s k - (e : K)‖ < (3 : ℝ) ^ (-(Nat.log 3 64 : ℤ)))
  let E := Finset.univ.biUnion near
  have hmem : a ∈ E := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha,hZ⟩, near_named hi⟩⟩
  refine ⟨c, hroot, E, hmem, ?_, ?_⟩
  · have lone : ∀ k, (near k).card ≤ 1 := by
      intro k
      apply Finset.card_le_one.mpr
      intro u hu v hv
      obtain ⟨hur,hu'⟩ := Finset.mem_filter.mp hu
      obtain ⟨hvr,hv'⟩ := Finset.mem_filter.mp hv
      exact near1 3 K (s k) 64 u v (Finset.mem_Icc.mp hur).1 (Finset.mem_Icc.mp hur).2
        (Finset.mem_Icc.mp hvr).1 (Finset.mem_Icc.mp hvr).2 hu' hv'
    calc E.card ≤ ∑ k : Fin r, (near k).card := Finset.card_biUnion_le
         _ ≤ ∑ _ : Fin r, 1 := Finset.sum_le_sum fun k _ => lone k
         _ = r := by simp
         _ ≤ R := hcap
  · intro e he heZ hnot m F _ _ _ hF
    have away : ∀ k, (3 : ℝ) ^ (-(Nat.log 3 64 : ℤ)) ≤ ‖s k - (e : K)‖ := by
      intro k
      apply le_of_not_gt
      intro hk
      exact hnot (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨he,heZ⟩, hk⟩⟩)
    apply (hfar e he m F hF (Nat.log 3 64) away).trans
    exact_mod_cast Nat.mul_le_mul_right _ hcap

theorem tower_filter_at_one {R : ℕ} {L : Type} [Field L] [NumberField L]
    (tower : Tower.IsTower 3 L R) (supply : ∀ S, Tower.IsTower 3 L S → ABound 3 S L) :
    ∃ c : ℕ, (∃ ζ : L, IsPrimitiveRoot ζ (3 ^ c)) ∧
      ∃ E : Finset ℕ, 1 ∈ E ∧ FirstBound 3 (R+1) c L 64 E :=
  named_filter (tower_can_name tower supply 1) (by decide) (by decide)

theorem cutoff : (3 : ℝ) ^ (-(Nat.log 3 64 : ℤ)) = 1 / 27 := by
  have h : Nat.log 3 64 = 3 := by decide
  rw [h]
  norm_num

/-- Integer residues have integral valuations. The ambient center field need not. -/
theorem strict_integer {z : ℤ} :
    ‖(z : ℚ_[3])‖ < (3 : ℝ) ^ (-(Nat.log 3 64 : ℤ)) ↔ (81 : ℤ) ∣ z := by
  have hlog : Nat.log 3 64 = 3 := by decide
  rw [hlog]
  have eq := Padic.norm_int_le_pow_iff_dvd (p := 3) z 4
  change ‖(z : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-(4 : ℤ)) ↔ (81 : ℤ) ∣ z at eq
  rw [← eq]
  by_cases h : z = 0
  · subst z
    norm_num
  · have hz : (z : ℚ_[3]) ≠ 0 := by exact_mod_cast h
    rw [Padic.norm_eq_zpow_neg_valuation hz, show ((3 : ℕ) : ℝ) = 3 by norm_num,
      zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3),
      zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)]
    omega

/-- An isometric coefficient embedding transfers the integer-center test to the ambient field. -/
theorem integer_center_iff (K : Type) [NormedField K] [NormedAlgebra ℚ_[3] K] (u v : ℤ) :
    ‖(u : K) - (v : K)‖ < (3 : ℝ) ^ (-(Nat.log 3 64 : ℤ)) ↔ (81 : ℤ) ∣ (u - v) := by
  have h : (u : K) - v = algebraMap ℚ_[3] K ((u - v : ℤ) : ℚ_[3]) := by
    push_cast
    simp
  rw [h, norm_algebraMap']
  exact strict_integer

/-- The published construction embeds integral centers into ℚ₃. This covers every such center. -/
theorem integral_center_iff (s : ℤ_[3]) (e : ℕ) :
    ‖(s : ℚ_[3]) - (e : ℚ_[3])‖ < (3 : ℝ) ^ (-(Nat.log 3 64 : ℤ)) ↔
      PadicInt.toZModPow 4 s = (e : ZMod (3 ^ 4)) := by
  let x : ℤ_[3] := s - e
  have hn : ‖(s : ℚ_[3]) - (e : ℚ_[3])‖ = ‖x‖ := by
    simp [x, PadicInt.norm_def]
  have hcut : ‖x‖ < (3 : ℝ) ^ (-(Nat.log 3 64 : ℤ)) ↔
      ‖x‖ ≤ ((3 : ℕ) : ℝ) ^ (-((4 : ℕ) : ℤ)) := by
    rw [show Nat.log 3 64 = 3 by decide]
    by_cases hx : x = 0
    · simp [hx]
    · rw [PadicInt.norm_eq_zpow_neg_valuation hx, show ((3 : ℕ) : ℝ) = 3 by norm_num,
        zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3),
        zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)]
      omega
  rw [hn, hcut, PadicInt.norm_le_pow_iff_mem_span_pow x 4, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
  simp [x, sub_eq_zero]

/-- Copy the source's union for the concrete coefficient field of its exhibited centers. -/
noncomputable def integralWeights {r : ℕ} (s : Fin r → ℤ_[3]) : Finset ℕ := by
  classical
  exact Finset.univ.biUnion fun i => (Finset.Icc 1 64).filter fun e : ℕ =>
    ‖(s i : ℚ_[3]) - (e : ℚ_[3])‖ < (3 : ℝ) ^ (-(Nat.log 3 64 : ℤ))

theorem weights_by_residue {r : ℕ} (s : Fin r → ℤ_[3]) (e : ℕ) :
    e ∈ integralWeights s ↔ 1 ≤ e ∧ e ≤ 64 ∧ ∃ i, PadicInt.toZModPow 4 (s i) = (e : ZMod (3 ^ 4)) := by
  classical
  simp only [integralWeights, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_filter, Finset.mem_Icc, integral_center_iff]
  aesop

theorem boundary_control : ¬ ‖(27 : ℚ_[3])‖ < (3 : ℝ) ^ (-(Nat.log 3 64 : ℤ)) ∧
    ‖(27 : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-(Nat.log 3 64 : ℤ)) := by
  constructor
  · simpa only [Int.cast_ofNat] using (mt (@strict_integer 27).mp (by decide))
  · have hlog : Nat.log 3 64 = 3 := by decide
    rw [hlog]
    exact (Padic.norm_int_le_pow_iff_dvd (p := 3) 27 3).2 (by decide)

end SlotThree

#print axioms SlotThree.firstBound_insert
#print axioms SlotThree.can_mark_after_exc
#print axioms SlotThree.awayBound_cons
#print axioms SlotThree.forget_named
#print axioms SlotThree.name_with_second
#print axioms SlotThree.tower_succ
#print axioms SlotThree.tower_can_name
#print axioms SlotThree.near_named
#print axioms SlotThree.cutoff
#print axioms SlotThree.named_filter
#print axioms SlotThree.tower_filter_at_one
#print axioms SlotThree.strict_integer
#print axioms SlotThree.integer_center_iff
#print axioms SlotThree.integral_center_iff
#print axioms SlotThree.weights_by_residue
#print axioms SlotThree.boundary_control
