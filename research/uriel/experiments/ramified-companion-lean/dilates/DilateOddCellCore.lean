import DilateDefs

/-! At uniformizer precision 2r+1 the fine coefficient quotient S(r+1)
has precisely two scalar residues per cell. Keep that final bit explicit. -/
noncomputable section
namespace RamDilate.OddCell
open TargetOne Finset

abbrev pi {A : Type*} [CommRing A] : QuadraticAlgebra A 2 0 := QuadraticAlgebra.omega

theorem pi_sq {A : Type*} [CommRing A] : (pi : QuadraticAlgebra A 2 0)^2=2 := by
  rw [pow_two,QuadraticAlgebra.omega_mul_omega_eq_mk]; rfl

def center (r : ℕ) : S (r+1) := ((2^r : ℕ) : S (r+1))

private theorem top_two (r : ℕ) (z : ZMod (2^(r+1))) :
    (2^r : ZMod (2^(r+1)))*z = 0 ∨ (2^r : ZMod (2^(r+1)))*z = 2^r := by
  have hz : (2^r : ZMod (2^(r+1)))*2=0 := by
    rw [←pow_succ, ←Nat.cast_ofNat (R := ZMod (2^(r+1))) (n:=2), ←Nat.cast_pow]
    exact ZMod.natCast_self _
  have hv : z = (z.val%2:ℕ) + (2:ZMod (2^(r+1)))*(z.val/2:ℕ) := by
    rw [←Nat.cast_ofNat (R:=ZMod (2^(r+1))) (n:=2),←Nat.cast_mul,←Nat.cast_add]
    rw [show z.val%2 + 2*(z.val/2)=z.val by omega, ZMod.natCast_zmod_val]
  rw [hv,mul_add,←mul_assoc,hz,zero_mul,add_zero]
  rcases (show z.val%2=0 ∨ z.val%2=1 by omega) with he|he <;> simp [he]

private theorem ideal_product (r : ℕ) (z : S (r+1)) :
    (pi^(2*r+1))*z = (⟨0,(2^r)*z.re⟩ : S (r+1)) := by
  have hz : (2^r : ZMod (2^(r+1)))*2=0 := by
    rw [←pow_succ, ←Nat.cast_ofNat (R := ZMod (2^(r+1))) (n:=2), ←Nat.cast_pow]
    exact ZMod.natCast_self _
  have hsp : (2:S (r+1))^r=((2^r:ℕ):S (r+1)) := by push_cast; rfl
  rw [pow_succ (pi : S (r+1)) (2*r),pow_mul,pi_sq,hsp,mul_assoc]
  obtain ⟨a,b⟩ := z
  rw [QuadraticAlgebra.omega_mul_mk]
  apply QuadraticAlgebra.ext <;>
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,QuadraticAlgebra.re_natCast,QuadraticAlgebra.im_natCast]
  · simp [←mul_assoc,hz]
  · simp

private theorem generator (r : ℕ) : (pi^(2*r+1) : S (r+1)) = center r*pi := by
  rw [pow_succ,pow_mul,pi_sq,center,Nat.cast_pow,Nat.cast_ofNat]

/-- In the fine ring the image of the ideal (π^(2r+1)) is exactly its zero
and its generator, so the indicated congruence class has two children. -/
theorem children (r : ℕ) (s : S (r+1)) :
    pi^(2*r+1) ∣ s-center r ↔ s=center r ∨ s=center r*(1+pi) := by
  constructor
  · rintro ⟨z,hz⟩
    rw [ideal_product] at hz
    rcases top_two r z.re with h|h
    · left
      rw [h] at hz
      exact sub_eq_zero.mp hz
    · right
      rw [h] at hz
      have hg := ideal_product r (1:S (r+1))
      simp only [mul_one,QuadraticAlgebra.re_one] at hg
      rw [←hg,generator] at hz
      linear_combination hz
  · rintro (rfl|rfl)
    · simp
    · refine ⟨1,?_⟩
      rw [generator]; ring

theorem distinct (r : ℕ) : center r ≠ center r*(1+pi) := by
  have hne : (2^r : ZMod (2^(r+1))) ≠ 0 := by
    intro h
    have he : ((2^r:ℕ):ZMod (2^(r+1)))=0 := by simpa only [Nat.cast_pow,Nat.cast_ofNat] using h
    have hlt : (2:ℕ)^r < 2^(r+1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self r)
    exact (Nat.not_dvd_of_pos_of_lt (by positivity) hlt) ((ZMod.natCast_eq_zero_iff ..).mp he)
  intro he
  have h : center r*pi=0 := by linear_combination -he
  rw [←generator] at h
  have hh := ideal_product r (1:S (r+1))
  rw [h,zero_mul] at hh
  exact hne (by simpa only [QuadraticAlgebra.im_zero,QuadraticAlgebra.re_one,mul_one]
    using (congrArg QuadraticAlgebra.im hh).symm)

/-- Fine vectors are counted once if their sum of squares has the prescribed
odd-depth residue. The target cell has two fine digits. -/
def mixedCount (r : ℕ) (a : S (r+1)) : ℕ :=
  Nat.card {x : Fin 6 → S (r+1) // pi^(2*r+1) ∣ sqSum x-a}

theorem mixed_sum (r : ℕ) :
    mixedCount r (center r) = count 6 (center r) + count 6 (center r*(1+pi)) := by
  classical
  let : Fintype (S (r+1)) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  let b := center r
  let c := center r*(1+pi)
  have diff : b≠c := distinct r
  let e : {x : Fin 6 → S (r+1) // pi^(2*r+1) ∣ sqSum x-b} ≃
      ({x : Fin 6 → S (r+1) // sqSum x=b} ⊕ {x : Fin 6 → S (r+1) // sqSum x=c}) :=
    {toFun := fun x => if h : sqSum x.1=b then Sum.inl ⟨x.1,h⟩ else
        Sum.inr ⟨x.1,((children r _).mp x.2).resolve_left h⟩
     invFun := Sum.elim (fun x => ⟨x.1,(children r _).mpr (Or.inl x.2)⟩)
       (fun x => ⟨x.1,(children r _).mpr (Or.inr x.2)⟩)
     left_inv := fun x => by dsimp only; split <;> rfl
     right_inv := fun x => by
       rcases x with x|x
       · simp [x.2]
       · have hn : sqSum x.1 ≠ b := fun h => diff (h.symm.trans x.2)
         simp [hn]}
  exact (Nat.card_congr e).trans (Nat.card_sum ..)

theorem mixed_scaled (r : ℕ) (a : S (r+1)) (u : (S (r+1))ˣ) :
    mixedCount r ((u:S (r+1))^2*a) = mixedCount r a := by
  symm
  let e := Equiv.piCongrRight fun _ : Fin 6 => u.mulLeft
  apply Nat.card_congr (Equiv.subtypeEquiv e ?_)
  intro x
  have he : sqSum (e x)=(u:S (r+1))^2*sqSum x := by
    change (∑ i, ((u:S (r+1))*x i)^2) = _ * (∑ i, x i^2)
    simp [Finset.mul_sum,mul_pow]
  rw [he,←mul_sub,(u.isUnit.pow 2).dvd_mul_left]

end RamDilate.OddCell
#print axioms RamDilate.OddCell.mixed_sum
#print axioms RamDilate.OddCell.mixed_scaled
