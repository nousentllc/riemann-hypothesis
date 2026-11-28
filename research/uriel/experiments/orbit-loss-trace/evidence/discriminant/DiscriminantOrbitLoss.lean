import Formalism.SizeWindowBrackets.ChainSlopeWindows.DiscriminantSettingSatisfied

/-!
# Removing the served-orbit omission from the pinned discriminant ledger

The ten size estimates hold under the original window and large-scale assumptions.
For the actual loss functional, we retain the original joint hypotheses and also
assume that its weighted bad-point count is zero. The proof below follows the
formal ledger in DiscriminantSettingSatisfied, separating its one changed term.
-/

namespace Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.OrbitAudit

open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas
open Formalism.LFunctionChainParameters.LErr
open Formalism.LFunctionChainParameters.PrimeWindowSizeBounds

theorem served_omission_zero (τ : Type) (Ps PR : Finset ℕ) (cl : ℕ → PClass)
    (TT : Finset τ) (TTp : ℕ → Finset τ) (BAD : ℕ → τ → Prop)
    (m a : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a)
    (hzero : badPrimeLogWeightedCount PR TT BAD = 0)
    (hBad : ∀ p ∈ Ps, cl p = PClass.served → ∀ t ∈ TT \ TTp p, p ∈ PR ∧ BAD p t) :
    (∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
      4 * m * a * (Real.log p / p) * ((TT \ TTp p).card : ℝ)) = 0 := by
  apply le_antisymm
  · simpa only [mul_zero] using
      out_discriminant_bound τ Ps PR cl TT TTp BAD m a 0 hm ha hzero.le hBad
  · apply Finset.sum_nonneg
    intro p _
    have h := logdiv_nonneg p
    positivity

theorem ten_surviving_bounds {P : Par} {e K m T : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K) (hm : 0 ≤ m)
    (hT : 1 ≤ T) : tDetD P m T - tOutD P m T ≤ (2 * Real.log 4 * P.C + 12 * sg P K) * unitU P m T := by
  have a1 := size_floors_bound P e K m T hW hL hm hT
  have a2 := size_cp_bucket_bound P e K m T hW hL hm hT
  have a3 := size_prime_low_bound P e K m T hW hL hm hT
  have a4 := size_prime_high_bound P e K m T hW hL hm hT
  have a5 := size_or_bucket_bound P e K m T hW hL hm hT
  have a7 := size_orders_bucket_bound P e K m T hW hL hm hT
  have a8 := size_band_bound P e K m T hW hL hm hT
  have a9 := size_high_bucket_bound P e K m T hW hL hm hT
  have a10 := size_discriminant_bound P e K m T hW hL hm hT
  have a11 := sizeSecond_core hW hL hm hT
  unfold tDetD
  linarith

/-- The original source names this lower bound. Its expansion of the high-prime
bucket contains a nonnegative leading term that survives every orbit placement. -/
theorem high_prime_floor : SizePrHighLower := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have hC := F.C0
  have hX := F.Xpos.le
  have hη := F.η0
  have hSc := F.Sc0
  have hbn := div_nonneg F.b0 F.npos.le
  have hlx := F.lx0
  have hw : 0 ≤ w8 := by linarith only [F.w81]
  have ht := F.t0
  have hbo := F.bo0
  have low : P.C * P.b ≤ P.Xp * P.Q₂ := by
    rw [xprime_q_two_expand F]
    have e1 : 0 ≤ P.C * X * (P.η + P.Sc) := by positivity
    have e2 : 0 ≤ P.C * (P.b / P.n) * P.lx * w8 := by positivity
    have e3 : 0 ≤ P.C * X * P.t * P.lx * w8 := by positivity
    have e4 : 0 ≤ X * P.bo := by positivity
    linarith only [e1, e2, e3, e4]
  have hT0 : 0 ≤ T := by linarith
  have scaled := mul_le_mul_of_nonneg_left low
    (show 0 ≤ m * T * (2 * Real.log 4) by have := log_four_nonneg; positivity)
  unfold unitU tPrHigh
  linarith only [scaled]

/-- The exact budgeted omission cap relative to the common unit, in product form
so that zero rank or cardinality never requires division. -/
theorem normalized_omission (P : Par) (m T : ℝ) (hx : 0 < P.x) :
    tOutD P m T = (4 * P.x ^ (-1 + P.ε)) * unitU P m T := by
  have ha : P.a = P.x * P.b := rfl
  have hp : P.x * P.x ^ (-2 + P.ε) = P.x ^ (-1 + P.ε) := by
    calc
      _ = P.x ^ (1 : ℝ) * P.x ^ (-2 + P.ε) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hx]; congr 1; ring
  unfold tOutD unitU
  rw [ha, ← hp]
  ring

theorem joint_weighted_mass : ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ (P : Par) (e K : ℝ), P.Cord = Cord → Windows P e K →
    LargeX P.x P.ε e K →
    ∀ (ι κ τ U : Type) (Ps cand PR : Finset ℕ) (J : Finset κ) (TT : Finset τ)
      (BAD : ℕ → τ → Prop) (Sig : ℕ → ℝ) (io : U → ℕ → ℝ) (D : U → LD ι κ τ),
      PrimeClassLossHypotheses P Ps cand PR J TT BAD Sig io D →
      ∀ υ, (D υ).ASK P.d Ps J TT - (D υ).Ga J ≤
        (2 * Real.log 4 * P.C + 12 * sg P K) * unitU P J.card TT.card
        + 4 * P.a * J.card * badPrimeLogWeightedCount PR TT BAD := by
  obtain ⟨C₁, hC₁⟩ := first_kind_bound
  refine ⟨max C₁ 0, le_max_right _ _, ?_⟩
  intro P e K hCord hW hL ι κ τ U Ps cand PR J TT BAD Sig io D hS
  obtain ⟨hTT, hPs, hSig0, hWW, _, _, hAll⟩ := hS
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, -⟩ :=
    side_condition_of_windows P e K hW hL
  have hm : (0 : ℝ) ≤ (J.card : ℝ) := Nat.cast_nonneg _
  have hT : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hTT
  have hT0 : (0 : ℝ) ≤ (TT.card : ℝ) := Nat.cast_nonneg _
  have ha0 : 0 ≤ P.a := F.apos.le
  intro υ
  obtain ⟨hLed, hFirst, hSecond, hBad⟩ := hAll υ
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hLed
  have led := loss_bound ι κ τ (D υ).W (D υ).below (D υ).l Ps (D υ).cl J TT (D υ).TTp
    (D υ).Iex (D υ).at_ (D υ).wz (D υ).Id (D υ).wd P.d (D υ).gainW (D υ).tauW
    (D υ).gain (D υ).tau (D υ).lo (D υ).fl P.a P.th P.wpp P.Xpp P.Xp P.C P.f P.N P.Sk P.Q₁ P.Q₂
    P.lx P.La P.k P.K₀ (D υ).L₁ P.p₀ l1 (fun p hp => (hPs p hp).1) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10
    s11 s12 s13 s14 s15 s16 s17 s18 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11
  have out := out_discriminant_bound τ Ps PR (D υ).cl TT (D υ).TTp BAD J.card P.a _ hm ha0 (le_refl _) hBad
  have first := first_le hC₁ (by rw [hCord]; exact le_max_left _ _) hW hL Ps (D υ).cl hPs hFirst
    J.card TT.card hm hT0
  have second := second_discriminant_bound Ps cand (D υ).cl Sig P.θ J.card TT.card P.a _ hm hT0 ha0 hSig0 hWW hSecond
  have size := ten_surviving_bounds hW hL hm hT
  unfold tDetD tFloors tCp tPrLow tPrHigh tOr tHigh tD tOutD tSecondD at size
  unfold LD.ASK LD.Ga
  linarith

theorem joint_zero_mass : ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ (P : Par) (e K : ℝ), P.Cord = Cord → Windows P e K →
    LargeX P.x P.ε e K →
    ∀ (ι κ τ U : Type) (Ps cand PR : Finset ℕ) (J : Finset κ) (TT : Finset τ)
      (BAD : ℕ → τ → Prop) (Sig : ℕ → ℝ) (io : U → ℕ → ℝ) (D : U → LD ι κ τ),
      PrimeClassLossHypotheses P Ps cand PR J TT BAD Sig io D →
      badPrimeLogWeightedCount PR TT BAD = 0 →
      ∀ υ, (D υ).ASK P.d Ps J TT - (D υ).Ga J ≤
        (2 * Real.log 4 * P.C + 12 * sg P K) * unitU P J.card TT.card := by
  obtain ⟨Cord, hCord, h⟩ := joint_weighted_mass
  refine ⟨Cord, hCord, ?_⟩
  intro P e K hC hW hL ι κ τ U Ps cand PR J TT BAD Sig io D hS hzero υ
  simpa only [hzero, mul_zero, add_zero] using
    h P e K hC hW hL ι κ τ U Ps cand PR J TT BAD Sig io D hS υ

set_option pp.fullNames true

#print axioms high_prime_floor
#print axioms normalized_omission
#print axioms joint_weighted_mass
#print axioms ten_surviving_bounds
#print axioms served_omission_zero
#print axioms joint_zero_mass

end Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.OrbitAudit
