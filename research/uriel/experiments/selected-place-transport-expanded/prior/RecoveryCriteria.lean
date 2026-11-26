import HostComparison

open New Formalism.HC Formalism.FrobeniusOrbits
noncomputable section
namespace FixedDatum

/-- The multiplier in 2(d+1) = q₀ t must be odd. -/
theorem odd_multiplier (P : Parameters) :
    ∃ t : ℕ, 2 * (P.d + 1) = P.q₀ * t ∧ t % 2 = 1 := by
  obtain ⟨t, ht⟩ := P.q₀_dvd_and_not_dvd.1
  refine ⟨t, ht, ?_⟩
  by_contra h
  have hv : t = 2 * (t / 2) := by omega
  apply P.q₀_dvd_and_not_dvd.2
  refine ⟨t / 2, ?_⟩
  calc
    P.d + 1 = 2 * (P.d + 1) / 2 := by omega
    _ = (P.q₀ * t) / 2 := by rw [ht]
    _ = P.q₀ * (t / 2) := by
      conv_lhs => rw [hv]
      rw [show P.q₀ * (2 * (t / 2)) = 2 * (P.q₀ * (t / 2)) by ring]
      omega

/-- The missed case of the original congruence test is sufficient for all five prime clauses. -/
theorem seven_iff (P : Parameters) : P.d % 16 = 7 ↔ ¬ 32 ∣ P.q₀ := by
  constructor
  · intro h hd
    have := hd.trans P.q₀_dvd_and_not_dvd.1
    omega
  · intro h
    obtain ⟨u,hu⟩ := (by decide : 16 ∣ 18480).trans P.dvd_q₀
    obtain ⟨t,ht,hot⟩ := odd_multiplier P
    have hou : u % 2 = 1 := by omega
    have hut : (u * t) % 2 = 1 := by rw [Nat.mul_mod, hou, hot]
    rw [hu, Nat.mul_assoc] at ht
    omega

theorem jacobi_at_eleven (P : Parameters) : jacobiSym (-(P.d : ℤ)) 11 = 1 := by
  have h := ((by decide : 11 ∣ 18480).trans P.dvd_q₀).trans P.q₀_dvd_and_not_dvd.1
  have hm : (-(P.d : ℤ)) % 11 = 1 := by omega
  rw [jacobiSym.mod_left, show ((11 : ℕ) : ℤ) = 11 from rfl, hm, jacobiSym.one_left]

theorem eleven_iff (P : Parameters) : HostHyp 11 P.d ↔ ¬ 32 ∣ P.q₀ := by
  constructor
  · intro h
    exact (seven_iff P).mp h.2.2.2.1
  · intro h
    exact ⟨by decide, P.d_prime, by decide, (seven_iff P).mpr h, jacobi_at_eleven P⟩

theorem any_prime_iff (P : Parameters) : (∃ q, HostHyp q P.d) ↔ ¬ 32 ∣ P.q₀ := by
  constructor
  · rintro ⟨q,hq⟩
    exact (seven_iff P).mp hq.2.2.2.1
  · intro h
    exact ⟨11, (eleven_iff P).mpr h⟩

/-- With the uniform auxiliary prime, the readable modulus cannot be absorbed in QS. -/
theorem conductor_component {φ : Frame} (H : HostRaw φ) (P : Parameters) (hq : H.q = 11) :
    ¬ P.q₀ ∣ H.QS := by
  intro hd
  have hleft := ((by decide : 11 ∣ 18480).trans P.dvd_q₀).trans hd
  have hright : 11 ∣ H.q * H.d := by rw [hq]; exact dvd_mul_right _ _
  have bad := Nat.dvd_gcd hleft hright
  rw [H.QS_coprime.gcd_eq_one] at bad
  norm_num at bad

/-- The old sign kernel keeps exactly the first sign and the A-index. -/
def signedIndices (φ : Frame) : φ.Psi ≃ ℤˣ × φ.A where
  toFun g := (g.val.1.1, φ.iotaInv g.val.2)
  invFun z := ⟨((z.1, 1), φ.iota z.2), (Frame.mem_Psi_iff _).mpr rfl⟩
  left_inv := by
    rintro ⟨⟨⟨u,v⟩,a⟩,h⟩
    have hv : v = 1 := (Frame.mem_Psi_iff _).mp h
    subst v
    rfl
  right_inv := by intro z; rfl

/-- A field identification permits a bare finite bijection onto signed indices.
    The conclusion makes no assertion about residues, cosets or weights. -/
theorem mere_signed_bijection {P : Parameters} (D : Data P) {φ : Frame}
    (H : HostAx φ) (e : H.E ≃ₐ[ℚ] D.E) : Nonempty (D.Φ ≃ φ.Psi) := by
  classical
  have hc : Fintype.card D.Φ = Fintype.card (ℤˣ × φ.A) := by
    rw [Fintype.card_prod, Fintype.card_units_int, place_count D H e]
  exact ⟨(Fintype.equivOfCardEq hc).trans (signedIndices φ).symm⟩

end FixedDatum
#print axioms FixedDatum.any_prime_iff
#print axioms FixedDatum.eleven_iff
#print axioms FixedDatum.signedIndices
#print axioms FixedDatum.mere_signed_bijection
#print axioms FixedDatum.conductor_component
