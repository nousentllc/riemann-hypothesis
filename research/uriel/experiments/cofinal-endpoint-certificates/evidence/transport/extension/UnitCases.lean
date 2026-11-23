import MarkedWindows
import Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG
import Development.AutomorphicArithmetic.PrimitiveCosets.GzEq

open Formalism.HC UpperTheory.Top Formalism.MainNotions Formalism.BasicNotions GlobalTheory.EX

namespace MarkedWindows

theorem principalCap {c : ℕ} (lo : 1 ≤ c) (hi : c ≤ Nat.card (Subgroup.zpowers PChar.one.χ)) : c = 1 := by
  have hcard : Nat.card (Subgroup.zpowers PChar.one.χ) = 1 := by
    change Nat.card (Subgroup.zpowers (1 : DirichletCharacter ℂ 1)) = 1
    simp
  omega

theorem principalLevel (y : ℝ) : (Level.cyc PChar.one).Gm y = Deduction.G y := by
  classical
  have h : (Level.cyc PChar.one).KEPT = {PChar.one} := by
    ext ψ
    rw [Level.cyc, Level.mem_ofSub, Finset.mem_singleton]
    constructor
    · rintro ⟨χ,hχ,rfl⟩
      have eq : χ = 1 := by
        change χ ∈ Subgroup.zpowers (1 : DirichletCharacter ℂ 1) at hχ
        rw [Subgroup.zpowers_one_eq_bot] at hχ
        exact (Subgroup.mem_bot).1 hχ
      rw [eq, PChar.of_one]
    · rintro rfl
      exact ⟨1, Subgroup.one_mem _, PChar.of_one _⟩
  have hz : (Level.cyc PChar.one).Nt = ∅ := by simp [Level.Nt,h]
  rw [Level.Gm,hz]
  simpa using (UpperTheory.Comparison₂.Gz_eq y).1.trans (UpperTheory.Comparison₂.Gz_eq y).2

theorem winPairsUnit (ψ : PChar) (eps : ℝ) (hε : 0 < eps) (h52 : eps < 1/52)
    (hV : VWinAt ψ 401) (hP : PairEx) :
    ∃ J : ℝ, 1 ≤ J ∧ ∀ y : ℝ, ∃ Z : ℝ, y ≤ Z ∧ ∀ x : ℝ, Z ≤ x → x ≤ Z^(2:ℝ) →
      ∃ (Y : ℝ) (q d e : ℕ), WinDatum ψ eps J 1 x Y q d e := by
  obtain ⟨e,he⟩ := exists_pageN eps hε
  obtain ⟨J,hJ,k,hk,hka,T,ht⟩ := rawSupply ψ eps 1 hε h52 le_rfl hV hP e he
  have hk0 : 0 ≤ k := by linarith
  have ha : 2+8*eps ≠ 0 := by linarith
  have hone : k = 1 := by
    calc k = (k^(2+8*eps))^((2+8*eps)⁻¹) := (Real.rpow_rpow_inv hk0 ha).symm
         _ = _ := by rw [hka, Real.one_rpow]
  subst k
  simp only [one_mul,div_one] at ht
  have hj : 0 < J := by linarith
  refine ⟨J,hJ,fun y => ?_⟩
  let M := max 1 y
  have hm0 : 0 ≤ M := zero_le_one.trans (le_max_left _ _)
  let X := max T (M^J)
  have hm : M ≤ X^(1/J) := by
    calc M = (M^J)^(1/J) := by rw [one_div,Real.rpow_rpow_inv hm0 hj.ne']
         _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hm0 _) (le_max_right _ _) (one_div_nonneg.2 hj.le)
  obtain ⟨W,q,d,hw,hWX,hall⟩ := ht X (le_max_left _ _)
  refine ⟨W, (le_max_right _ y).trans (hm.trans hw), fun x hl hr => ?_⟩
  exact ⟨_,q,d,_,hall x hl (le_min (hr.trans hWX) hr)⟩

theorem winsFor (ψ : PChar) (eps lam : ℝ) (c : ℕ) (hε : 0 < eps) (h52 : eps < 1/52)
    (hc : 1 ≤ c) (hcap : c ≤ Nat.card (Subgroup.zpowers ψ.χ))
    (hl : lam < 2 ∨ lam = 2 ∧ ψ = PChar.one) (hV : VWinAt ψ 401) (hP : PairEx) :
    ∃ J : ℝ, 1 ≤ J ∧ ∀ y : ℝ, ∃ Z : ℝ, y ≤ Z ∧ ∀ x : ℝ, Z ≤ x → x ≤ Z^lam →
      ∃ (Y : ℝ) (q d e : ℕ), WinDatum ψ eps J c x Y q d e := by
  rcases hl with hl | ⟨rfl,rfl⟩
  · exact winPairsBelowTwo ψ eps c lam hε h52 (by exact_mod_cast hc) hl hV hP
  · have eq := principalCap hc hcap
    subst c
    simpa using winPairsUnit PChar.one eps hε h52 hV hP

/-- A strengthened copy of the original predicate, with an equality for that same scale system. -/
def MarkedHost (ψ : PChar) (la : ℝ) (P : HostReq) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1/52 → ∃ CT2 C8 C5 c6 Cb x0 : ℝ,
    1 ≤ C8 ∧ 0 < C5 ∧ 0 < c6 ∧ 0 < Cb ∧ ∃ S : Scales la,
      (∃ c : ℕ, 1 ≤ c ∧ c ≤ Nat.card (Subgroup.zpowers ψ.χ) ∧
        S.Win = {x | ∃ Y q d e, WinDatum ψ eps S.J c x Y q d e}) ∧
      ∀ s : Scale, s.eps = eps → x0 ≤ s.x → S.Mem s →
        ∃ (R : Ranks) (H : Host R) (q0 : ℕ), RankVal s R ∧ H.CT2 = CT2 ∧ HostGood s C8 C5 c6 Cb H q0 ∧ P C5 s R H q0

theorem MarkedHost.forget {ψ : PChar} {la : ℝ} {P : HostReq} (h : MarkedHost ψ la P) : HostExW la P := by
  intro eps he h52
  obtain ⟨u,v,w,y,z,t,hu,hv,hw,hy,S,_,hS⟩ := h eps he h52
  exact ⟨u,v,w,y,z,t,hu,hv,hw,hy,S,hS⟩

end MarkedWindows

#print axioms MarkedWindows.principalCap
#print axioms MarkedWindows.principalLevel
#print axioms MarkedWindows.winPairsUnit
#print axioms MarkedWindows.winsFor
#print axioms MarkedWindows.MarkedHost.forget
