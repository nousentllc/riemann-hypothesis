import RamBase
import RamLift
import RamField

/-! Project the complete depth-five census to its coarser quotients. This
produces independent small-depth anchors without enumerating all vectors. -/
open Finset TargetOne
noncomputable section
namespace RamDilate

local instance : Fintype RamBase.R :=
  Fintype.ofEquiv _ RamBase.equiv.symm

/-- The two sides count the same fine vectors. On the left one first chooses
a coarse solution, on the right one first chooses a fine target. -/
private theorem project {B : Type} [CommRing B] [Fintype B] [DecidableEq B]
    (f : RamBase.R →+* B) (t : ℕ)
    (hflat : ∀ b : B, Nat.card {x : RamBase.R // f x=b} = t) (b : B) :
    count 6 b * t^6 =
      ∑ z : RamBase.R, if f z = b then count 6 z else 0 := by
  classical
  let small := univ.filter fun y : Fin 6 → B => sqSum y=b
  let targets := univ.filter fun z : RamBase.R => f z=b
  let g (x : Fin 6 → RamBase.R) (i : Fin 6) := f (x i)
  have hs : small.card=count 6 b := by
    simp [count,small,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have h1 := TargetFour.partitions g small
  have h2 := TargetFour.partitions (@sqSum RamBase.R _ 6) targets
  have agree (x : Fin 6 → RamBase.R) : g x ∈ small ↔ sqSum x ∈ targets := by
    change _ ∈ Finset.filter _ _ ↔ _ ∈ Finset.filter _ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    change (∑ i, (f (x i))^2) = b ↔ f (∑ i, x i^2) = b
    rw [map_sum]; simp only [map_pow]
  have he : Nat.card {x // g x ∈ small}=Nat.card {x : Fin 6 → RamBase.R // sqSum x ∈ targets} :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (fun x => agree x))
  have lifts (y : Fin 6 → B) : Nat.card {x // g x=y}=t^6 := by
    let e : {x // g x=y} ≃ ((i : Fin 6) → {z : RamBase.R // f z=y i}) :=
      {toFun := fun x i => ⟨x.1 i,congrFun x.2 i⟩
       invFun := fun x => ⟨fun i => (x i).1,funext fun i => (x i).2⟩
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl}
    rw [Nat.card_congr e,Nat.card_pi]
    simp only [hflat,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simp only [lifts,sum_const,nsmul_eq_mul,hs,Nat.cast_id] at h1
  change _ = ∑ z ∈ targets, count 6 z at h2
  rw [←h1,he,h2]
  dsimp only [targets]
  rw [Finset.sum_filter]

/-- Explicit finite sum, with only its 32-by-32 target alphabet enumerated. -/
def projectedTotal {B : Type} [CommRing B] [DecidableEq B] (f : RamBase.R →+* B) (b : B) : ℕ :=
  RamBase.addUp (fun i => RamBase.addUp (fun j =>
    let z : RamBase.R := ⟨i,j⟩
    if f z=b then RamBase.row6 (RamBase.repNo (RamBase.encode z)) else 0) 32) 32

theorem project_total {B : Type} [CommRing B] [Fintype B] [DecidableEq B]
    (f : RamBase.R →+* B) (t : ℕ)
    (hflat : ∀ b : B, Nat.card {x : RamBase.R // f x=b} = t) (b : B) :
    count 6 b * t^6 = projectedTotal f b := by
  rw [project f t hflat b]
  let h (z : RamBase.R) := if f z=b then count 6 z else 0
  change ∑ z : RamBase.R, h z = _
  rw [←RamBase.equiv.symm.sum_comp h,Fintype.sum_prod_type,projectedTotal,RamBase.addUp_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [RamBase.addUp_eq]
  apply Finset.sum_congr rfl
  intro j _
  have he : RamBase.equiv.symm (i,j) = (⟨(i.val:ZMod 32),(j.val:ZMod 32)⟩ : RamBase.R) := by
    apply QuadraticAlgebra.ext <;> exact (ZMod.natCast_zmod_val _).symm
  dsimp only [h]
  rw [he,RamBase.census_six]

set_option maxRecDepth 5000
set_option maxHeartbeats 0

theorem low3_four : count 6 (4 : RamField.R 3) = 2155872256 := by
  let : Fintype (RamField.R 3) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  have h := project_total (RamLift.reduce 8 4) 16 (RamLift.scalar_count 8 4) (4 : RamField.R 3)
  have e : projectedTotal (RamLift.reduce 8 4) (4 : RamField.R 3) = 36169534507319296 := by decide +kernel
  exact Nat.eq_of_mul_eq_mul_right (by decide) (h.trans e)

theorem low4_four : count 6 (4 : RamField.R 4) = 2207613190144 := by
  let : Fintype (RamField.R 4) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  have h := project_total (RamLift.reduce 16 2) 4 (RamLift.scalar_count 16 2) (4 : RamField.R 4)
  have e : projectedTotal (RamLift.reduce 16 2) (4 : RamField.R 4) = 9042383626829824 := by decide +kernel
  exact Nat.eq_of_mul_eq_mul_right (by decide) (h.trans e)

theorem low4_eight : count 6 (8 : RamField.R 4) = 2199560126464 := by
  let : Fintype (RamField.R 4) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  have h := project_total (RamLift.reduce 16 2) 4 (RamLift.scalar_count 16 2) (8 : RamField.R 4)
  have e : projectedTotal (RamLift.reduce 16 2) (8 : RamField.R 4) = 9009398277996544 := by decide +kernel
  exact Nat.eq_of_mul_eq_mul_right (by decide) (h.trans e)

theorem low3_eight : count 6 (8 : RamField.R 3) = 2147483648 := by
  let : Fintype (RamField.R 3) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  have h := project_total (RamLift.reduce 8 4) 16 (RamLift.scalar_count 8 4) (8 : RamField.R 3)
  have e : projectedTotal (RamLift.reduce 8 4) (8 : RamField.R 3) = 36028797018963968 := by decide +kernel
  exact Nat.eq_of_mul_eq_mul_right (by decide) (h.trans e)

theorem low2_four : count 6 (4 : RamField.R 2) = 2097152 := by
  let : Fintype (RamField.R 2) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  have h := project_total (RamLift.reduce 4 8) 64 (RamLift.scalar_count 4 8) (4 : RamField.R 2)
  have e : projectedTotal (RamLift.reduce 4 8) (4 : RamField.R 2) = 144115188075855872 := by decide +kernel
  exact Nat.eq_of_mul_eq_mul_right (by decide) (h.trans e)

theorem low2_zero : count 6 (0 : RamField.R 2) = 2097152 := by
  let : Fintype (RamField.R 2) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  have h := project_total (RamLift.reduce 4 8) 64 (RamLift.scalar_count 4 8) (0 : RamField.R 2)
  have e : projectedTotal (RamLift.reduce 4 8) (0 : RamField.R 2) = 144115188075855872 := by decide +kernel
  exact Nat.eq_of_mul_eq_mul_right (by decide) (h.trans e)

theorem low3_zero : count 6 (0 : RamField.R 3) = 2147483648 := by
  let : Fintype (RamField.R 3) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  have h := project_total (RamLift.reduce 8 4) 16 (RamLift.scalar_count 8 4) (0 : RamField.R 3)
  have e : projectedTotal (RamLift.reduce 8 4) (0 : RamField.R 3) = 36028797018963968 := by decide +kernel
  exact Nat.eq_of_mul_eq_mul_right (by decide) (h.trans e)

theorem low4_zero : count 6 (0 : RamField.R 4) = 2199023255552 := by
  let : Fintype (RamField.R 4) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  have h := project_total (RamLift.reduce 16 2) 4 (RamLift.scalar_count 16 2) (0 : RamField.R 4)
  have e : projectedTotal (RamLift.reduce 16 2) (0 : RamField.R 4) = 9007199254740992 := by decide +kernel
  exact Nat.eq_of_mul_eq_mul_right (by decide) (h.trans e)

end RamDilate
#print axioms RamDilate.low3_four
#print axioms RamDilate.low4_eight
