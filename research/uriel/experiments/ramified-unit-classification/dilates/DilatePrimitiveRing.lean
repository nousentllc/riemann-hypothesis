import DilatePrimitivePivot
import RamLift

noncomputable section
namespace RamDilate.PrimitiveRing
open RamLift (B)
open TargetOne (sqSum)
def odd {n : ℕ} (z : B n) : Prop := z.re.val % 2 ≠ 0
abbrev V (n : ℕ) := {x : Fin 6 → B n // ∃ i, odd (x i)}
def C (n : ℕ) (b : B n) := Nat.card {x : V n // sqSum x.1=b}

private def rearrange (n : ℕ) (b : B n) :
    {x : V n // sqSum x.1=b} ≃ {x : Fin 6 → B n // sqSum x=b ∧ ∃ i, odd (x i)} where
  toFun x := ⟨x.1.1,x.2,x.1.2⟩
  invFun x := ⟨⟨x.1,x.2.2⟩,x.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

private abbrev π (n : ℕ) : B n := QuadraticAlgebra.omega
private theorem pi_sq (n : ℕ) : (π n)^2=2 := by
  rw [pow_two,QuadraticAlgebra.omega_mul_omega_eq_mk]; rfl
private theorem pi_nil (k : ℕ) : IsNilpotent (π (32*2^k)) := by
  have h : (2:ZMod (32*2^k))^(k+5)=0 := by
    have hnat : 2^(k+5)=32*2^k := by ring
    exact_mod_cast (show (((2^(k+5):ℕ):ZMod (32*2^k)))=0 by rw [hnat]; exact ZMod.natCast_self _)
  have hh := congrArg (algebraMap (ZMod (32*2^k)) (B (32*2^k))) h
  simp only [map_pow,map_ofNat,map_zero] at hh
  exact ⟨2*(k+5),by rw [pow_mul,pi_sq,hh]⟩

private theorem decomp {n : ℕ} [NeZero n] (z : B n) : ∃ w : B n, z = (z.re.val % 2 : ℕ) + π n * w := by
  refine ⟨⟨z.im,(z.re.val / 2 : ℕ)⟩, ?_⟩
  have h := congrArg (fun t : ℕ => (t : ZMod n)) (Nat.mod_add_div z.re.val 2)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val] at h
  apply QuadraticAlgebra.ext
  · simpa [π,QuadraticAlgebra.omega,QuadraticAlgebra.re_mul] using h.symm
  · simp [π,QuadraticAlgebra.omega,QuadraticAlgebra.im_mul]

private theorem odd_unit (k : ℕ) (z : B (32*2^k)) : odd z ↔ IsUnit z := by
  obtain ⟨w,hw⟩ := decomp z
  have hn := (Commute.all (π (32*2^k)) w).isNilpotent_mul_right (pi_nil k)
  haveI : Fact (1 < 32*2^k) := ⟨by have := Nat.two_pow_pos k; omega⟩
  constructor
  · intro h
    have h1 : z.re.val%2=1 := by unfold odd at h; omega
    rw [hw,h1,Nat.cast_one]
    exact hn.isUnit_one_add
  · contrapose!
    intro h
    have h0 : z.re.val%2=0 := by simpa [odd] using h
    rw [hw,h0,Nat.cast_zero,zero_add]
    exact hn.not_isUnit

theorem constant (k : ℕ) (b w : B (32*2^k)) :
    C (32*2^k) b = C (32*2^k) (b+8*w) := by
  classical
  let A := B (32*2^k)
  let π' := π (32*2^k)
  have h6 : π'^6=8 := by calc π'^6 = (π'^2)^3 := by ring
                               _ = 8 := by rw [pi_sq]; norm_num
  haveI : Fintype A := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  obtain ⟨e,he⟩ := Pivot.scalar_perm π' (pi_nil k) (pi_sq _) (π'*w)
  let φ : Aˣ ≃ {z : A // odd z} :=
    { toFun := fun u => ⟨u,(odd_unit k u).2 u.isUnit⟩
      invFun := fun x => ((odd_unit k x.1).1 x.2).unit
      left_inv := fun u => Units.ext ((odd_unit k u).1 ((odd_unit k u).2 u.isUnit)).unit_spec
      right_inv := fun x => Subtype.ext ((odd_unit k x.1).1 x.2).unit_spec }
  let E := Equiv.Perm.extendDomain e φ
  have hp (z : A) : odd (E z) ↔ odd z := by
    by_cases hz : odd z
    · exact iff_of_true (by rw [show E z= _ from Equiv.Perm.extendDomain_apply_subtype e φ hz]; exact (φ _).property) hz
    · rw [show E z=z from Equiv.Perm.extendDomain_apply_not_subtype e φ hz]
  have hs (z : A) (hz : odd z) : (E z)^2=z^2+8*w := by
    rw [show E z= _ from Equiv.Perm.extendDomain_apply_subtype e φ hz]
    have h := he (φ.symm ⟨z,hz⟩)
    have hz' : (φ.symm ⟨z,hz⟩ : A) = z := ((odd_unit k z).1 hz).unit_spec
    change (↑(e (φ.symm ⟨z,hz⟩)) : A)^2 = _
    rw [h,hz']
    linear_combination w*h6
  unfold C
  rw [Nat.card_congr (rearrange _ b), Nat.card_congr (rearrange _ (b+8*w))]
  exact Pivot.primitive_shift odd E hp hs b
end RamDilate.PrimitiveRing
