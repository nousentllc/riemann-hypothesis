import SuccessiveFields
import Development.AutomorphicArithmetic.CharacterBoxes.TwistForm
open NumberField Formalism.GaloisCohomology Formalism.HC UpperTheory.Top UpperTheory.V
  UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win EndpointWeights CoherentFields
  UpperTheory.V.Base UpperTheory.V.HV
noncomputable section
namespace SynchronizedSlots

/-- Physical scale factor one. At the later canonical query a genuine PairGood supplies
every prime guard. The only discrete tests still requested are at the two endpoints. -/
theorem gapWinDatum (wA wB : ℝ) (K : BConst) (eps : ℝ) (psi : PChar)
    (heps : 0 < eps) (heps52 : eps < 1/52)
    (hwA : 0 ≤ wA*eps/K.CK) (hwB : 0 ≤ wB*eps/K.CK)
    (hj : Across K wA wB 401) (hp : PointHV) (hc : ThmBc 401)
    (e : ℝ → ℕ) (hpage : ∀ x ≥ (1:ℝ), PageN eps x (e x))
    (D : Finset ℕ) (direct : ∀ x ≥ (1:ℝ), BbAt K D (Lchi psi) eps (fun y => ⌊y^(401:ℝ)⌋₊) x) :
    ∃ T : ℝ, ∃ EB : ℕ → ℕ → Finset ℕ,
    (∀ l ∈ Bchi psi, OnOldRange (EB l)) ∧
    (∀ l ∈ Bchi psi, ∀ Z, (EB l Z).card ≤ K.Rl l (Lchi psi l)) ∧
    ∀ q d : ℕ, PrimePair psi.N q d → ∃ EA : ℕ → Finset ℕ,
    OnOldRange EA ∧ (∀ Z, (EA Z).card ≤ K.R0 (AbF.ofChar psi)) ∧
    ∀ (U X a b : ℝ), 0 ≤ U → U ≤ X → T ≤ X → a ≤ b →
    a ≤ U → X^(1/Jchi K 401 eps psi) ≤ a → b ≤ X →
    PairGood psi.N eps (X^(1/Jchi K 401 eps psi)) X q d →
    b^(wA*eps/K.CK) < (⌊a^(401:ℝ)⌋₊ : ℝ) → b^(wB*eps/K.CK) < (⌊a^(401:ℝ)⌋₊ : ℝ) →
    ActiveSmall (wA*eps/K.CK) (EA ⌊U^(401:ℝ)⌋₊) ⌊a^(401:ℝ)⌋₊ a →
    ActiveSmall (wA*eps/K.CK) (EA ⌊X^(401:ℝ)⌋₊) ⌊b^(401:ℝ)⌋₊ b →
    (∀ l ∈ Bchi psi, l ∉ D → ActiveSmall (wB*eps/K.CK) (EB l ⌊U^(401:ℝ)⌋₊) ⌊a^(401:ℝ)⌋₊ a) →
    (∀ l ∈ Bchi psi, l ∉ D → ActiveSmall (wB*eps/K.CK) (EB l ⌊X^(401:ℝ)⌋₊) ⌊b^(401:ℝ)⌋₊ b) →
    ∀ x, a ≤ x → x ≤ b → WinDatum psi eps (Jchi K 401 eps psi) 1 x (X^(1/Jchi K 401 eps psi)) q d (e x) := by
  set J := Jchi K 401 eps psi
  have hJ : 0 < J := BConst.J_pos K (by norm_num) heps _ _ _
  obtain ⟨r₁,r₂,L,X0,EB,coB,capB,pairs⟩ := gapVAt wA wB K 401 eps psi (by norm_num) heps heps52 hwA hwB hj hp hc e hpage D direct
  let indices := [psi.N, ordC psi, pK psi, hStar psi, pOne psi, r₁, r₂]
  obtain ⟨XB,hXB⟩ := eventually_winPair_gt_power eps J 401 (indices.sum : ℝ) heps hJ
  obtain ⟨Y0,hY0⟩ := log_mul_le_rpow_of_winPair eps heps
  set T := max 2 (max L Y0)
  have hT : 2 ≤ T := le_max_left _ _
  have hTL : L ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hTY : Y0 ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨max (max X0 XB) (T ^ J), EB, coB, capB, ?_⟩
  intro q d hpair
  obtain ⟨EA,coA,capA,main⟩ := pairs q d hpair
  refine ⟨EA,coA,capA,?_⟩
  intro U X a b hU huX hX hab haU hlowA hbX pg ca cb haA hbA haB hbB x hax hxb
  have hw := pg.pair
  have hX0 : X0 ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hXB' : XB ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hTX : T^J ≤ X := (le_max_right _ _).trans hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hTX
  have hlow : T ≤ X ^ (1/J) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith : 0 ≤ T) J) hTX (by positivity : 0 ≤ 1/J)
    rwa [← Real.rpow_mul (by linarith : 0 ≤ T), mul_one_div_cancel hJ.ne', Real.rpow_one] at h
  obtain ⟨hq,hd,hPq,hPd⟩ := hXB X hXB' q d hw
  have hlist : ∀ k ∈ indices, k < q ∧ k < d := by
    intro k hk
    have hsum : k ≤ indices.sum := List.le_sum_of_mem hk
    have hcast : (k:ℝ) ≤ (indices.sum:ℝ) := by exact_mod_cast hsum
    exact ⟨by exact_mod_cast hcast.trans_lt hPq, by exact_mod_cast hcast.trans_lt hPd⟩
  have hlog := hY0 _ (hTY.trans hlow) q d hw
  have hpow : (X^(1/J))^(eps/4) = X^(eps/(4*J)) := by
    rw [← Real.rpow_mul hXpos.le]
    congr 1
    field_simp
  rw [hpow] at hlog
  have hxX := hxb.trans hbX
  have hx2 := hT.trans (hlow.trans (hlowA.trans hax))
  have hv := main U X a b _ hU huX hX0 (hTL.trans (hlow.trans hlowA)) hab haU hlowA hbX hw hq hd hlist hlog ca cb haA hbA haB hbB x hax hxb
  have hxp : 1 ≤ x := by linarith
  have page := hpage x hxp
  refine ⟨Real.rpow_le_rpow (by linarith) hxX (one_div_nonneg.2 hJ.le),
    hlowA.trans hax, pg.mono hxX, by simpa using page.1, by simpa using page.2, ?_⟩
  intro E _ _ hE
  exact (hv E hE).mono (Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hxp (by norm_num : (400:ℝ) ≤ 401))) le_rfl

end SynchronizedSlots
end
#print axioms SynchronizedSlots.gapWinDatum
