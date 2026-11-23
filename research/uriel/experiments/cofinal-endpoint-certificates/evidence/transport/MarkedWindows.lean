import Development.AutomorphicArithmetic.CharacterBoxes.TwistForm
import Development.AutomorphicArithmetic.PrimitiveCosets.LevelGmLeOnFamilyScales

open Formalism.HC UpperTheory.Top Formalism.MainNotions Formalism.BasicNotions

namespace MarkedWindows

/-- The pointwise adapter. The field input can come from any verified estimate at u. -/
theorem localDatum {ψ : PChar} {eps J c Y X k u : ℝ} {q d n : ℕ}
    (hε : 0 < eps) (hk : 1 ≤ k) (hu : 1 ≤ u)
    (hc : k ^ (2 + 8 * eps) = c) (hscale : k ^ (400 : ℝ) ≤ u)
    (hlo : (k*u) ^ (1/J) ≤ Y) (hup : Y ≤ k*u) (hx : k*u ≤ X)
    (hp : PairGood ψ.N eps Y X q d) (hn : PageN eps u n)
    (hv : VAt ψ eps 401 q d n u) : WinDatum ψ eps J c (k*u) Y q d n := by
  have hk0 : 0 ≤ k := by linarith
  have hu0 : 0 < u := by linarith
  have hc0 : 0 ≤ c := hc ▸ Real.rpow_nonneg hk0 _
  have hpow : (k*u) ^ (2+8*eps) = c * u^(2+8*eps) := by rw [Real.mul_rpow hk0 hu0.le, hc]
  refine ⟨hlo, hup, hp.mono hx, ?_, ?_, ?_⟩
  · rw [hpow]
    exact mul_le_mul_of_nonneg_left hn.1 hc0
  · rw [hpow]
    calc _ ≤ c * (2 * u ^ (2+8*eps)) := mul_le_mul_of_nonneg_left hn.2 hc0
         _ = _ := by ring
  · intro E _ _ hE
    apply (hv E hE).mono
    · apply Nat.floor_mono
      rw [Real.mul_rpow hk0 hu0.le, show (401 : ℝ) = 1 + 400 by norm_num,
        Real.rpow_add hu0, Real.rpow_one]
      exact mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hu0.le _)
    · exact Real.sqrt_le_sqrt (Real.exp_le_exp.2 (Real.rpow_le_rpow hu0.le
        (le_mul_of_one_le_left hu0.le hk) hε.le))

/-- One fixed page function and the same constants for every sufficiently large outer scale. -/
theorem rawSupply (ψ : PChar) (eps c : ℝ) (hε : 0 < eps) (h52 : eps < 1/52)
    (hc : 1 ≤ c) (hV : VWinAt ψ 401) (hP : PairEx)
    (e : ℝ → ℕ) (he : ∀ u ≥ (1:ℝ), PageN eps u (e u)) :
    ∃ J : ℝ, 1 ≤ J ∧ ∃ k : ℝ, 1 ≤ k ∧ k ^ (2+8*eps) = c ∧ ∃ T : ℝ,
      ∀ X ≥ T, ∃ (W : ℝ) (q d : ℕ), X^(1/J) ≤ W ∧ W^(2:ℝ) ≤ X ∧
      ∀ x : ℝ, k*W ≤ x → x ≤ min X (k*W^(2:ℝ)) →
        WinDatum ψ eps J c x (X^(1/J)) q d (e (x/k)) := by
  obtain ⟨J,hJ,X0,hX0⟩ := hV eps hε h52 e he
  obtain ⟨Y1,hY1⟩ := hP ψ.N (Nat.pos_of_ne_zero (NeZero.ne _)) eps J hε h52 hJ
  have ha : 0 < 2 + 8 * eps := by linarith
  let k := c ^ (1/(2+8*eps))
  have hk : 1 ≤ k := Real.one_le_rpow hc (one_div_nonneg.2 ha.le)
  have hk0 : 0 < k := by linarith
  have hka : k^(2+8*eps) = c := by
    dsimp [k]; rw [one_div, Real.rpow_inv_rpow (by linarith : 0 ≤ c) ha.ne']
  let M := max 1 (max Y1 (k^(400:ℝ)))
  have hM : 1 ≤ M := le_max_left _ _
  have hJ0 : 0 < J := by linarith
  refine ⟨J,hJ,k,hk,hka,max X0 (M^J),fun X hX => ?_⟩
  have hXM := (le_max_right _ _).trans hX
  have hM0 : 0 ≤ M := by linarith
  have hXpos : 0 ≤ X := (Real.rpow_nonneg hM0 J).trans hXM
  have hMY : M ≤ X^(1/J) := by
    calc M = (M^J)^(1/J) := by rw [one_div, Real.rpow_rpow_inv hM0 hJ0.ne']
         _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hM0 _) hXM (one_div_nonneg.2 hJ0.le)
  have hid : (X ^ (1/J))^J = X := by rw [one_div, Real.rpow_inv_rpow hXpos hJ0.ne']
  obtain ⟨q,d,hpg⟩ := hY1 _ (((le_max_left Y1 _).trans (le_max_right 1 _)).trans hMY)
  rw [hid] at hpg
  obtain ⟨W,hYW,hWX,hWV⟩ := hX0 X ((le_max_left _ _).trans hX) q d hpg.pair
  have hMW := hMY.trans hYW
  have hWp : 0 < W := by linarith
  refine ⟨W,q,d,hYW,hWX,fun x hleft hright => ?_⟩
  obtain ⟨hx,hku⟩ := le_min_iff.1 hright
  have huw : W ≤ x/k := (le_div_iff₀ hk0).2 (by simpa [mul_comm] using hleft)
  have huu : x/k ≤ W^(2:ℝ) := (div_le_iff₀ hk0).2 (by simpa [mul_comm] using hku)
  have heq : k*(x/k) = x := by field_simp
  have hlo : x^(1/J) ≤ X^(1/J) := Real.rpow_le_rpow (by nlinarith [mul_pos hk0 hWp]) hx (one_div_nonneg.2 hJ0.le)
  have hup : X^(1/J) ≤ x := hYW.trans ((le_mul_of_one_le_left hWp.le hk).trans hleft)
  have hku' : k^(400:ℝ) ≤ x/k := (((le_max_right Y1 _).trans (le_max_right 1 _)).trans hMW).trans huw
  have hu := (hM.trans hMW).trans huw
  simpa only [heq] using localDatum hε hk hu hka hku' (by rwa [heq]) (by rwa [heq])
    (by rwa [heq]) hpg (he _ hu) (hWV _ huw huu)

/-- Exact geometric tradeoff for the guaranteed W² right edge. -/
theorem widthRoom {k W lam : ℝ} (hk : 1 ≤ k) (hW : 1 ≤ W) (hl : lam < 2)
    (hroom : k ^ (lam / (2-lam)) ≤ W) : (k*W)^lam ≤ W^(2:ℝ) := by
  have hk0 : 0 ≤ k := by linarith
  have hW0 : 0 < W := by linarith
  have hd : 0 < 2-lam := by linarith
  have h : k^lam ≤ W^(2-lam) := by
    calc k^lam = (k^(lam/(2-lam)))^(2-lam) := by rw [← Real.rpow_mul hk0]; congr 1; field_simp
         _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hk0 _) hroom hd.le
  rw [Real.mul_rpow hk0 hW0.le]
  calc k^lam * W^lam ≤ W^(2-lam) * W^lam := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hW0.le _)
       _ = _ := by rw [← Real.rpow_add hW0]; ring_nf

/-- The original WinDatum and both original hypotheses at any fixed power below two. -/
theorem winPairsBelowTwo (ψ : PChar) (eps c lam : ℝ) (hε : 0 < eps) (h52 : eps < 1/52)
    (hc : 1 ≤ c) (hl : lam < 2) (hV : VWinAt ψ 401) (hP : PairEx) :
    ∃ J : ℝ, 1 ≤ J ∧ ∀ y : ℝ, ∃ Z : ℝ, y ≤ Z ∧ ∀ x : ℝ, Z ≤ x → x ≤ Z ^ lam →
      ∃ (Y : ℝ) (q d e : ℕ), WinDatum ψ eps J c x Y q d e := by
  obtain ⟨e,he⟩ := exists_pageN eps hε
  obtain ⟨J,hJ,k,hk,_,T,ht⟩ := rawSupply ψ eps c hε h52 hc hV hP e he
  have hj : 0 < J := by linarith
  refine ⟨J,hJ,fun y => ?_⟩
  let M := max 1 (max y (k^(lam/(2-lam))))
  have h1 : 1 ≤ M := le_max_left _ _
  have h0 : 0 ≤ M := by linarith
  let X := max T (M^J)
  have hX := le_max_right T (M^J)
  have hm : M ≤ X^(1/J) := by
    calc M = (M^J)^(1/J) := by rw [one_div, Real.rpow_rpow_inv h0 hj.ne']
         _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg h0 _) hX (one_div_nonneg.2 hj.le)
  obtain ⟨W,q,d,hYW,hWX,hall⟩ := ht X (le_max_left _ _)
  have hMw := hm.trans hYW
  have hw := h1.trans hMw
  have hw0 : 0 ≤ W := by linarith
  have hroom : k^(lam/(2-lam)) ≤ W := ((le_max_right _ _).trans (le_max_right _ _)).trans hMw
  have hy : y ≤ W := ((le_max_left _ _).trans (le_max_right _ _)).trans hMw
  refine ⟨k*W,hy.trans (le_mul_of_one_le_left hw0 hk),fun x hx hx' => ?_⟩
  have hw2 := hx'.trans (widthRoom hk hw hl hroom)
  exact ⟨_, q, d, _, hall x hx (le_min (hw2.trans hWX)
    (hw2.trans (le_mul_of_one_le_left (Real.rpow_nonneg hw0 _) hk)))⟩

/-- Domain marking only. Explicit formula and all chained core inputs live on this same original family. -/
theorem markedComparison (Λ : Level) {eps eD eL : ℝ} (hε : 0 < eps) (Fm : FamP eps)
    (hE : EFamC Λ Fm.toFamCore)
    (hT : ChebyshevInequalityOnFamilyWindows (fun F : FamP _ => F.toFamCore) (fun F => ChainTied F) Fm eD eL)
    (Q : Set ℝ) (hQ : Q ⊆ Fm.Win) :
    ∃ T : ℝ, ∀ x ≥ T, x ∈ Q → Λ.Gm x ≤ x ^ ((1:ℝ)/2 + (eD+eL+7)*eps) := by
  obtain ⟨T,h⟩ := UpperTheory.Comparison₂.level_gm_le_on_family_scales Λ eD eL eps hε Fm hE hT
  exact ⟨T, fun x hx hq => h x hx (hQ hq)⟩

end MarkedWindows

#print axioms MarkedWindows.localDatum
#print axioms MarkedWindows.rawSupply
#print axioms MarkedWindows.widthRoom
#print axioms MarkedWindows.winPairsBelowTwo
#print axioms MarkedWindows.markedComparison
