import New.Reduction.OneSidedBound

open New Finset Filter
noncomputable section
namespace FixedDatum

def mainParameters : Parameters where
  q₀ := 36960
  d := 55439
  dvd_q₀ := by decide
  d_prime := by norm_num1
  q₀_dvd_and_not_dvd := by decide

def controlParameters : Parameters where
  q₀ := 18480
  d := 9239
  dvd_q₀ := by decide
  d_prime := by norm_num1
  q₀_dvd_and_not_dvd := by decide

def Realized (P : Parameters) (n : ℕ) : Prop :=
  ∃ D : Data P, D.natX = n

theorem realized_eventually (P : Parameters) : ∀ᶠ n : ℕ in atTop, Realized P n := by
  filter_upwards [eventually_exists_data_scales P (ε := 1/200) (by norm_num) (by norm_num)]
    with n ⟨D, hx, _⟩
  exact ⟨D, Nat.cast_injective (R := ℝ) (D.exp_logX.symm.trans hx)⟩

theorem common_exists : ∃ n : ℕ, Realized mainParameters n ∧ Realized controlParameters n :=
  ((realized_eventually mainParameters).and (realized_eventually controlParameters)).exists

open Classical in
def fixedN : ℕ := Nat.find common_exists

theorem fixed_spec : Realized mainParameters fixedN ∧ Realized controlParameters fixedN := by
  classical
  exact Nat.find_spec common_exists

def mainDatum : Data mainParameters := Classical.choose fixed_spec.1
def controlDatum : Data controlParameters := Classical.choose fixed_spec.2

theorem same_integer : mainDatum.natX = fixedN ∧ controlDatum.natX = fixedN :=
  ⟨Classical.choose_spec fixed_spec.1, Classical.choose_spec fixed_spec.2⟩

theorem fixed_bound : primeRemainder mainParameters.d mainParameters.q₀ fixedN ≤
    mainParameters.q₀.totient * mainDatum.logB ^ 6 / mainDatum.m +
    |primeRemainder mainParameters.d mainParameters.q₀ mainDatum.x₁| +
    mainDatum.logB * |primeRemainder mainParameters.d 1 mainDatum.x₁| := by
  simpa only [New.Data.x, mainDatum.exp_logX, same_integer.1] using mainDatum.primeRemainder_le

theorem at_least_one {P : Parameters} (D : Data P) : D.bPlaces.Nonempty := by
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  have H := D.towerDeg_le_card_bPlaces_mul
  rw [he] at H
  have hpos : 0 < towerDeg D.towerExp := by unfold towerDeg; positivity
  simp at H
  omega

/-- Translation by the inverse of the place of -1 lands in the identity residue fiber. -/
def translated {P : Parameters} (D : Data P) : D.bPlaces ↪ D.aPlaces where
  toFun t := ⟨(D.placeOfInt (-1))⁻¹ * t.val, by
    have hm : D.placeOfInt (-(1:ℕ) : ℤ) * ((D.placeOfInt (-1))⁻¹ * t.val) ∈ D.bPlaces := by
      simp
    exact (D.mem_aPlaces_iff_of_mul_mem_bPlaces hm).2 (by simp)⟩
  inj' := by intro a b h; exact Subtype.ext (mul_left_cancel (congrArg Subtype.val h))

theorem three_dvd_identity_fiber {P : Parameters} (D : Data P) : 3 ∣ D.aPlaces.card := by
  rw [D.card_aPlaces, towerDeg_eq]
  exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

theorem readable_degree {P : Parameters} (D : Data P) :
    Module.finrank ℚ D.E = 2 * Fintype.card D.Φ := by
  exact New.finrank_eq_two_mul_card_infinitePlace D.E

end FixedDatum
#print axioms FixedDatum.same_integer
#print axioms FixedDatum.fixed_bound
#print axioms FixedDatum.translated
