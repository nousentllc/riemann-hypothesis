import RamBasePivot
import FiniteCounts

/-! A shift of a primitive six-square target.  A scalar permutation shifts each
unit square by a prescribed element of (π⁵); its extension edits the first unit
coordinate. The first-unit rule is invariant under the edit. -/
noncomputable section
open Finset
namespace RamDilate.Pivot

variable {A : Type*} [CommRing A] [Finite A]

private theorem exists_shift (π : A) (hp : IsNilpotent π) (h2 : π^2=2)
    (u : Aˣ) (w : A) : ∃ v : Aˣ, (v:A)^2 = (u:A)^2 + π^5*w := by
  obtain ⟨y,hy⟩ := RamBase.five_digit_pivot π hp h2 u w
  have hn : IsNilpotent ((u⁻¹:Aˣ) * (π^3*y) : A) := by
    convert (Commute.all π ((↑(u⁻¹):A)*π^2*y)).isNilpotent_mul_right hp using 1 <;> ring
  have hv : IsUnit ((u:A)+π^3*y) := by
    convert u.isUnit.mul hn.isUnit_one_add using 1
    have hu := u.mul_inv
    linear_combination -(π^3*y)*hu
  exact ⟨hv.unit,by rwa [hv.unit_spec]⟩

private def rootEquiv (u v : Aˣ) :
    {z : Aˣ // (z:A)^2=(u:A)^2} ≃ {z : Aˣ // (z:A)^2=(v:A)^2} := by
  let k := v*u⁻¹
  apply Equiv.subtypeEquiv (Equiv.mulLeft k) ?_
  intro z
  change (z:A)^2=(u:A)^2 ↔ ((k:A)*(z:A))^2=(v:A)^2
  have hk : (k:A)*(u:A)=(v:A) := by simp [k,mul_assoc]
  rw [← hk, mul_pow, mul_pow]
  exact ((k.isUnit.pow 2).mul_right_inj).symm

private def liftRoots (π : A) (hp : IsNilpotent π) (h2 : π^2=2) (w c : A) :
    {z : Aˣ // (z:A)^2=c} ≃ {z : Aˣ // (z:A)^2-π^5*w=c} := by
  classical
  by_cases h : ∃ z : Aˣ, (z:A)^2=c
  · let u := h.choose
    have hu : (u:A)^2=c := h.choose_spec
    let v := (exists_shift π hp h2 u w).choose
    have hv : (v:A)^2=c+π^5*w := (exists_shift π hp h2 u w).choose_spec.trans (by rw [hu])
    exact (Equiv.subtypeEquivRight (fun z => by rw [hu])).trans <|
      (rootEquiv u v).trans (Equiv.subtypeEquivRight (fun z => by rw [hv]; constructor <;> intro hz <;> linear_combination hz))
  · haveI : IsEmpty {z : Aˣ // (z:A)^2=c} := ⟨fun z => h ⟨z.1,z.2⟩⟩
    haveI : IsEmpty {z : Aˣ // (z:A)^2-π^5*w=c} := ⟨fun z => by
      obtain ⟨v,hv⟩ := exists_shift π hp h2 z.1 (-w)
      exact h ⟨v,by rw [hv]; linear_combination z.2⟩⟩
    exact Equiv.equivOfIsEmpty _ _

theorem scalar_perm (π : A) (hp : IsNilpotent π) (h2 : π^2=2) (w : A) :
    ∃ e : Aˣ ≃ Aˣ, ∀ u : Aˣ, (e u:A)^2 = (u:A)^2 + π^5*w := by
  let f := fun z : Aˣ => (z:A)^2
  let g := fun z : Aˣ => (z:A)^2 - π^5*w
  let es : ∀ c, {z // f z=c} ≃ {z // g z=c} := liftRoots π hp h2 w
  exact ⟨Equiv.ofFiberEquiv es,fun u => by
    have h := Equiv.ofFiberEquiv_map es u
    change _ - _ = (u:A)^2 at h
    linear_combination h⟩

section first
variable {R : Type*} [CommRing R] (p : R → Prop) [DecidablePred p]
variable {d : ℕ}
private def first (x : Fin d → R) (i : Fin d) := p (x i) ∧ ∀ j < i, ¬p (x j)
private def edit (e : R ≃ R) (x : Fin d → R) (i : Fin d) : R := by
  classical exact if first p x i then e (x i) else x i
private theorem edit_flag (e : R ≃ R) (he : ∀ z, p (e z) ↔ p z)
    (x : Fin d → R) (i : Fin d) : p (edit p e x i) ↔ p (x i) := by
  classical
  unfold edit
  split <;> simp [he]
private theorem edit_first (e : R ≃ R) (he : ∀ z, p (e z) ↔ p z)
    (x : Fin d → R) (i : Fin d) : first p (edit p e x) i ↔ first p x i := by
  simp only [first, edit_flag p e he]
private def vecPerm (e : R ≃ R) (he : ∀ z, p (e z) ↔ p z) :
    (Fin d → R) ≃ (Fin d → R) where
  toFun := edit p e
  invFun := edit p e.symm
  left_inv x := by
    classical
    funext i
    change (if first p (edit p e x) i then _ else _) = _
    simp only [edit_first p e he x i]
    by_cases h : first p x i <;> simp [h,edit]
  right_inv x := by
    classical
    funext i
    have hs (z : R) : p (e.symm z) ↔ p z := by simpa using (he (e.symm z)).symm
    change (if first p (edit p e.symm x) i then _ else _) = _
    simp only [edit_first p e.symm hs x i]
    by_cases h : first p x i <;> simp [h,edit]

theorem primitive_shift {δ : R} (e : R ≃ R) (he : ∀ z, p (e z) ↔ p z)
    (hs : ∀ z, p z → (e z)^2=z^2+δ) (b : R) :
    Nat.card {x : Fin d → R // TargetOne.sqSum x=b ∧ ∃ i, p (x i)} =
    Nat.card {x : Fin d → R // TargetOne.sqSum x=b+δ ∧ ∃ i, p (x i)} := by
  classical
  apply Nat.card_congr (Equiv.subtypeEquiv (vecPerm p e he) ?_)
  intro x
  have hp : (∃ i, p (edit p e x i)) ↔ ∃ i, p (x i) := by simp only [edit_flag p e he]
  change _ ↔ TargetOne.sqSum (edit p e x)=_ ∧ ∃ i, p (edit p e x i)
  rw [hp]
  by_cases h : ∃ i, p (x i)
  · let s := Finset.univ.filter (fun i => p (x i))
    have hn : s.Nonempty := by simpa [s,Finset.Nonempty] using h
    let i := s.min' hn
    have hi : first p x i := by
      refine ⟨(Finset.mem_filter.mp (s.min'_mem hn)).2,fun j hj hpj => ?_⟩
      exact (not_le_of_gt hj) (s.min'_le j (by simp [s,hpj]))
    have unique (j : Fin d) (hji : j ≠ i) : ¬first p x j := by
      intro hj
      rcases lt_or_gt_of_ne hji with hlt|hgt
      · exact hi.2 _ hlt hj.1
      · exact hj.2 _ hgt hi.1
    have hsq (j : Fin d) : (edit p e x j)^2 = (x j)^2+(if j=i then δ else 0) := by
      by_cases hj : j=i
      · subst j; simpa [edit,hi] using hs (x i) hi.1
      · simp [edit,unique j hj,hj]
    have hsum : TargetOne.sqSum (edit p e x) = TargetOne.sqSum x + δ := by simp [TargetOne.sqSum,hsq,Finset.sum_add_distrib]
    simp [h,hsum]
  · simp [h]
end first
end RamDilate.Pivot
