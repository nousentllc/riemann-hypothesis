import SquareDepth
import FourEndpoint
open TargetOne HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped ENNReal NNReal TensorProduct Matrix
noncomputable section
namespace DyadicWave

theorem small_target (s h : ℕ) (N : Set K) (hN : N ∈ 𝓝 (s:K)) :
    ∃ k : ℕ, cylinder (k+h) (s:ZMod (2^(k+h))) ⊆ N := by
  have hcont : Continuous inc := continuous_subtype_val.comp ei.continuous
  have hpre : inc ⁻¹' N ∈ 𝓝 (s : ℤ_[2]) := by
    apply hcont.continuousAt
    simpa only [map_natCast] using hN
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2:ℝ)⁻¹ < 1)
  refine ⟨k,?_⟩
  rintro _ ⟨y,hy,rfl⟩
  apply hball
  have H : y ∈ Metric.closedBall (s : ℤ_[2]) ((2:ℝ)^(-((k+h:ℕ):ℤ))) := by
    rw [←ball_digit]
    simpa only [Set.mem_ofPred_eq,map_natCast] using hy
  have hh : (2:ℝ)^(-((k+h:ℕ):ℤ)) < ε := by
    rw [zpow_neg,zpow_natCast,←inv_pow]
    exact lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : k ≤ k+h)) hk
  exact Metric.closedBall_subset_ball hh H

theorem density_pos (k : ℕ) : 0 < density k := by
  have h : (1:ℚ) ≤ 16^k := one_le_pow₀ (by norm_num)
  unfold density
  have h' : 1/(4*(16:ℚ)^k)<1 := (div_lt_one (by positivity)).2 (by linarith)
  linarith

def massValue (k : ℕ) : ℝ≥0 := ⟨density k,by exact_mod_cast (density_pos k).le⟩

theorem late_tube (lam : Measure K) [lam.IsAddHaarMeasure] [SigmaFinite lam]
    (hlam : lam (O : Set K)=1) (k r u : ℕ) (hu : Odd u) (hr : 2*k+2 ≤ r) :
    (Measure.pi fun _ : Idx => lam) (tube r ((4^k*u^2:ℕ):ZMod (2^r))) =
        (massValue k:ℝ≥0∞)*lam (cylinder r ((4^k*u^2:ℕ):ZMod (2^r))) := by
  rw [tube_mass lam hlam,cyl_mass lam hlam]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_natCast,
    ENNReal.toReal_one,ENNReal.toReal_ofNat,ENNReal.coe_toReal]
  have h := with_unit k r u hu
  rw [if_neg (by omega)] at h
  unfold normCount at h
  have H : (count 6 ((4^k*u^2:ℕ):ZMod (2^r)):ℝ)/(2^r:ℝ)^5=(massValue k:ℝ) := by
    change _ = ((density k:ℚ):ℝ)
    simpa only [Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat] using congrArg (fun z : ℚ => (z:ℝ)) h
  field_simp at H ⊢
  linear_combination H

theorem fiber_mass (lam : Measure K) (hlam : IsStdV placeTwo lam)
    (m : H → Measure W) (hm : family lam m) (k u : ℕ) (hu : Odd u) :
    m (hermScal K conjG ((4^k*u^2:ℕ):K)) lattice=(massValue k:ℝ≥0∞) := by
  classical
  obtain ⟨i1,i2,i3,i4,-⟩ := locally
  have := hlam.1
  let s := 4^k*u^2
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hs0 : s ≠ 0 := by dsimp [s]; positivity
  have hsn : (s:K)≠0 := by
    have h := (map_ne_zero_iff (algebraMap ℚ K) (RingHom.injective _)).2 (Nat.cast_ne_zero.mpr hs0 : (s:ℚ) ≠ 0)
    simpa only [map_natCast] using h
  have hU : IsOpen ({0}ᶜ : Set K) := isOpen_compl_singleton
  have hs : (s:K) ∈ ({0}ᶜ : Set K) := hsn
  have h := local_mass_from_tests conjG isCM 3 J herm_id 2 gb placeTwo
    ((2:K) • (1 : Matrix Idx Idx K)) (trace_coords K) lam hlam m hm s (massValue k)
    {0}ᶜ hU hs (fun _ hz => hz) locally lattice_clopen.1 lattice_clopen.2
  have hval : (m (hermScal K conjG (s:K)) lattice).toReal=(massValue k:ℝ) := by
    apply h
    intro N hN
    obtain ⟨l,hc⟩ := small_target s (2*k+2) _ (Filter.inter_mem (hU.mem_nhds hs) hN)
    refine ⟨cylinder (l+(2*k+2)) s, compact_cylinder _ _,hc,?_,?_⟩
    · rw [Measure.real,cyl_mass lam hlam.2,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
      positivity
    · simp only [half_coord]
      exact late_tube lam hlam.2 k (l+(2*k+2)) u hu (by omega)
  have hp : 0 < (massValue k:ℝ) := by
    change (0:ℝ)<((density k:ℚ):ℝ)
    exact_mod_cast density_pos k
  have hfin : m (hermScal K conjG (s:K)) lattice ≠ ⊤ := by
    intro ht; rw [ht,ENNReal.toReal_top] at hval; linarith
  apply (ENNReal.toReal_eq_toReal_iff' hfin (by finiteness)).mp
  exact hval

theorem realized_all : ∃ lam : Measure K, IsStdV placeTwo lam ∧ ∃ m : H → Measure W,
    family lam m ∧ ∀ k u : ℕ, Odd u →
      m (hermScal K conjG ((4^k*u^2:ℕ):K)) lattice=(massValue k:ℝ≥0∞) := by
  obtain ⟨lam,hlam⟩ := standard_exists
  obtain ⟨m,hm,_⟩ := realized lam hlam
  exact ⟨lam,hlam,m,hm,fiber_mass lam hlam m hm⟩

end DyadicWave
#print axioms DyadicWave.realized_all
