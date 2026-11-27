import FourLift
import RamBasePivot

/-! Uniformity of the six-square census above the residue class 4 modulo 32.
The proof is in the quadratic ring itself, including its nilpotents. -/
open Finset TargetOne
noncomputable section
namespace RamLift

abbrev B (n : ℕ) := QuadraticAlgebra (ZMod n) 2 0
local instance (n : ℕ) [NeZero n] : Fintype (B n) :=
  Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm

def reduce (n t : ℕ) : B (n*t) →+* B n where
  toFun x := ⟨TargetFour.reduce n t x.re,TargetFour.reduce n t x.im⟩
  map_zero' := by ext <;> simp
  map_one' := by apply QuadraticAlgebra.ext <;> first | exact map_one _ | exact map_zero _
  map_add' x y := by ext <;> simp
  map_mul' x y := by apply QuadraticAlgebra.ext <;> simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,map_add,map_mul,map_zero,map_ofNat]

private theorem nil_two (k : ℕ) : IsNilpotent (2 : B (32*2^k)) := by
  refine ⟨k+5, ?_⟩
  have h : (2:ZMod (32*2^k))^(k+5)=0 := by
    have hnat : 2^(k+5)=32*2^k := by ring
    exact_mod_cast (show (((2^(k+5) : ℕ) : ZMod (32*2^k)))=0 by rw [hnat]; exact ZMod.natCast_self _)
  have hmap := congrArg (algebraMap (ZMod (32*2^k)) (B (32*2^k))) h
  simpa only [map_pow,map_ofNat,map_zero] using hmap

/-- The fifth uniformizer digit is where the linear displacement becomes a unit
multiple. The nonlinear term is one more digit deep. -/
theorem five_digits {R : Type*} [CommRing R] [Finite R] (π : R)
    (he : π^2=2) (hn : IsNilpotent π) (u : Rˣ) (w : R) :
    ∃ y : R, (↑u+π^3*y)^2=(u:R)^2+π^5*w :=
  RamBase.five_digit_pivot π hn he u w

private theorem orbit (k : ℕ) (b : B (32*2^k)) (hb : reduce 32 (2^k) b = 4) :
    ∃ u : (B (32*2^k))ˣ, b=(u:B (32*2^k))^2*4 := by
  let S := B (32*2^k)
  have hr : TargetFour.reduce 32 (2^k) b.re=4 := congrArg QuadraticAlgebra.re hb
  have hi : TargetFour.reduce 32 (2^k) b.im=0 := congrArg QuadraticAlgebra.im hb
  have rem (v : ZMod (32*2^k)) (t : ℕ) (ht : t<32)
      (he : TargetFour.reduce 32 (2^k) v = (t:ZMod 32)) :
      v.val % 32=t := by
    have hg : (v.val : ZMod 32)=(t:ZMod 32) := by
      rw [←ZMod.natCast_zmod_val v] at he
      simpa using he
    simpa [Nat.ModEq, Nat.mod_eq_of_lt ht] using (ZMod.natCast_eq_natCast_iff ..).mp hg
  have ar := rem b.re 4 (by decide) hr
  have ai := rem b.im 0 (by decide) (by simpa using hi)
  let w : S := ⟨(b.re.val / 32 : ℕ),(b.im.val / 32 : ℕ)⟩
  have hw : b=4+32*w := by
    have er : b.re.val=4+32*(b.re.val/32) := by omega
    have ei : b.im.val=32*(b.im.val/32) := by omega
    apply QuadraticAlgebra.ext
    · change b.re=4+(32*(↑(b.re.val/32))+2*0*(↑(b.im.val/32)))
      convert congrArg (fun n : ℕ => (n:ZMod (32*2^k))) er using 1 <;> simp
    · change b.im=0+(32*↑(b.im.val/32)+0*↑(b.re.val/32)+0*0*↑(b.im.val/32))
      convert congrArg (fun n : ℕ => (n:ZMod (32*2^k))) ei using 1 <;> simp
  let π : S := QuadraticAlgebra.omega
  have hp : π^2=2 := by rw [pow_two,QuadraticAlgebra.omega_mul_omega_eq_mk]; rfl
  have hn : IsNilpotent π := by
    obtain ⟨m,hm⟩ := nil_two k
    exact ⟨2*m,by rw [pow_mul,hp,hm]⟩
  obtain ⟨y,hy⟩ := five_digits π hp hn 1 (π*w)
  have hu : IsUnit (1+π^3*y) := by
    have hnil := (Commute.all π (π^2*y)).isNilpotent_mul_right hn
    convert hnil.isUnit_one_add using 1 <;> ring
  refine ⟨hu.unit,?_⟩
  rw [hu.unit_spec, hw]
  simp only [Units.val_one,one_pow] at hy
  rw [hy]
  have h6 : π^6=8 := by calc π^6 = (π^2)^3 := by ring
                         _ = 8 := by rw [hp]; norm_num
  linear_combination -4*w*h6

private def scalarEquiv (n t : ℕ) (b : B n) :
    {x : B (n*t) // reduce n t x=b} ≃
    {x : ZMod (n*t) // TargetFour.reduce n t x=b.re} ×
    {y : ZMod (n*t) // TargetFour.reduce n t y=b.im} where
  toFun x := (⟨x.1.re,congrArg QuadraticAlgebra.re x.2⟩,
    ⟨x.1.im,congrArg QuadraticAlgebra.im x.2⟩)
  invFun p := ⟨⟨p.1.1,p.2.1⟩,QuadraticAlgebra.ext p.1.2 p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem scalar_count (n t : ℕ) [NeZero n] [NeZero t] (b : B n) :
    Nat.card {a : B (n*t) // reduce n t a=b}=t^2 := by
  rw [Nat.card_congr (scalarEquiv n t b),Nat.card_prod,TargetFour.scalar_count,TargetFour.scalar_count,pow_two]

private def independent (n t : ℕ) (y : Fin 6 → B n) :
    {x : Fin 6 → B (n*t) // (fun i => reduce n t (x i))=y} ≃
      ((i : Fin 6) → {z : B (n*t) // reduce n t z=y i}) where
  toFun x i := ⟨x.1 i,congrFun x.2 i⟩
  invFun x := ⟨fun i => (x i).1,funext fun i => (x i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem orbit_count (k : ℕ) :
    count 6 (4 : B (32*2^k)) = count 6 (4 : B 32)*((2^k)^2)^5 := by
  classical
  let small := univ.filter fun y : Fin 6 → B 32 => sqSum y=4
  let targets := univ.filter fun t : B (32*2^k) => reduce 32 (2^k) t=4
  let r := fun (x : Fin 6 → B (32*2^k)) (i : Fin 6) => reduce 32 (2^k) (x i)
  have hs : small.card=count 6 (4:B 32) := by simp [count,small,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have ht : targets.card=(2^k)^2 := by
    change (univ.filter (fun t : B (32*2^k) => reduce 32 (2^k) t=4)).card = _
    convert scalar_count 32 (2^k) 4 using 1
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have fine : ∀ t ∈ targets, count 6 t = count 6 (4:B (32*2^k)) := by
    intro t ht
    obtain ⟨u,hu⟩ := orbit k t (Finset.mem_filter.mp ht).2
    rw [hu,TargetFour.scaled]
  have h1 := TargetFour.partitions r small
  have h2 := TargetFour.partitions (@sqSum (B (32*2^k)) _ 6) targets
  have hc (x : Fin 6 → B (32*2^k)) : r x ∈ small ↔ sqSum x ∈ targets := by
    change _ ∈ Finset.filter _ _ ↔ _ ∈ Finset.filter _ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    change (∑ i, (reduce 32 (2^k) (x i))^2)=4 ↔ reduce 32 (2^k) (∑ i,x i^2)=4
    rw [map_sum]; simp only [map_pow]
  have he : Nat.card {x // r x ∈ small}=Nat.card {x : Fin 6 → B (32*2^k) // sqSum x ∈ targets} :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (fun x => hc x))
  have lifts (y : Fin 6 → B 32) : Nat.card {x // r x=y}=((2^k)^2)^6 := by
    rw [Nat.card_congr (independent 32 (2^k) y), Nat.card_pi]
    simp only [scalar_count,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simp_rw [lifts] at h1
  change _ = ∑ s ∈ targets, count 6 s at h2
  rw [Finset.sum_congr rfl fine] at h2
  simp only [sum_const,nsmul_eq_mul,hs,ht] at h1 h2
  apply Nat.eq_of_mul_eq_mul_left (show 0<(2^k)^2 by positivity)
  calc _ = count 6 (4:B 32)*((2^k)^2)^6 := h2.symm.trans (he.symm.trans h1)
       _ = _ := by ring

theorem normalized_from_base
    (hbase : count 6 (4:B 32)=257*2^43) (k : ℕ) :
    128*count 6 (4:B (2^(k+5)))=257*((2^(k+5))^2)^5 := by
  rw [show 2^(k+5)=32*2^k by ring, orbit_count, hbase]
  ring
end RamLift
#print axioms RamLift.normalized_from_base
