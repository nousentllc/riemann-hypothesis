import HaarSlices
open Set MeasureTheory Topology Filter
open scoped ENNReal NNReal
noncomputable section
namespace CoordinateFloor
variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K]
  {ι : Type*} [Fintype ι]

/-- A nonzero constant slope at an integral isotropic centre gives a uniform
lower bound on all target tests in a fixed neighborhood of zero. -/
theorem lower (O : Subring K) (hOp : IsOpen (O : Set K)) (hOc : IsCompact (O : Set K))
    (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam O = 1)
    (Q slope : (ι → K) → K) (hQ : Continuous Q) (hS : Continuous slope)
    (e w : ι → K) (he : ∀ i, e i ∈ O) (hw : ∀ i, w i ∈ O)
    (hzero : Q w = 0) (hreg : slope w ≠ 0)
    (hline : ∀ x y, Q (x + y • e) = slope x * y + Q x) :
    ∃ D : Set K, IsOpen D ∧ (0 : K) ∈ D ∧ ∃ c : ℝ, 0 < c ∧
      ∀ V : Set K, MeasurableSet V → V ⊆ D →
        c * (lam V).toReal ≤ ((Measure.pi fun _ : ι => lam)
          {x | (∀ i, x i ∈ O) ∧ Q x ∈ V}).toReal := by
  classical
  let μ := Measure.pi fun _ : ι => lam
  let L : Set (ι → K) := Set.univ.pi fun _ => (O : Set K)
  have hLo : IsOpen L := isOpen_set_pi Set.finite_univ fun i _ => hOp
  have hLc : IsCompact L := isCompact_univ_pi fun _ => hOc
  have hwL : w ∈ L := fun i _ => hw i
  let δ := slope w
  let D : Set K := {t | t / δ ∈ O}
  have hDo : IsOpen D := hOp.preimage (continuous_id.div_const δ)
  have hzD : (0 : K) ∈ D := by simp [D]
  have hDc : IsCompact D := by
    have heq : D = (fun y : K => δ*y) '' (O : Set K) := by
      ext x
      constructor
      · intro h; exact ⟨x/δ,h,by field_simp [δ,hreg]⟩
      · rintro ⟨y,hy,rfl⟩
        change δ * y / δ ∈ O
        simpa [δ,hreg] using hy
    rw [heq]; exact hOc.image (continuous_const.mul continuous_id)
  have hd0 : 0 < lam D := hDo.measure_pos lam ⟨0,hzD⟩
  have hdf : lam D ≠ ⊤ := hDc.measure_lt_top.ne
  have h₁ : ∀ᶠ x in 𝓝 w, x ∈ L := hLo.mem_nhds hwL
  have h₂ : ∀ᶠ x in 𝓝 w, Q x ∈ D := hQ.continuousAt (hDo.mem_nhds (hzero ▸ hzD))
  have h₃ : ∀ᶠ x in 𝓝 w, slope x / δ ∈ O :=
    (hS.div_const δ).continuousAt (hOp.mem_nhds (by simpa [δ,hreg] using O.one_mem))
  have h₄ : ∀ᶠ x in 𝓝 w, δ / slope x ∈ O :=
    (continuousAt_const.div hS.continuousAt hreg) (hOp.mem_nhds (by simpa [δ,hreg] using O.one_mem))
  have h₅ : ∀ᶠ x in 𝓝 w, slope x ≠ 0 := hS.continuousAt (isOpen_compl_singleton.mem_nhds hreg)
  obtain ⟨W,hW,hWo,hwW⟩ := mem_nhds_iff.mp (h₁.and (h₂.and (h₃.and (h₄.and h₅))))
  have hWL : W ⊆ L := fun x hx => (hW hx).1
  have hW0 : 0 < μ W := hWo.measure_pos μ ⟨w,hwW⟩
  have hWf : μ W ≠ ⊤ := (measure_mono hWL |>.trans_lt hLc.measure_lt_top).ne
  let c := (μ W).toReal * (lam D).toReal⁻¹
  refine ⟨D,hDo,hzD,c,mul_pos (ENNReal.toReal_pos hW0.ne' hWf)
      (inv_pos.mpr (ENNReal.toReal_pos hd0.ne' hdf)),?_⟩
  intro V hV hVD
  let T := L ∩ Q ⁻¹' V
  have hT : MeasurableSet T := hLo.measurableSet.inter (hV.preimage hQ.measurable)
  have hTf : μ T ≠ ⊤ := (measure_mono inter_subset_left |>.trans_lt hLc.measure_lt_top).ne
  let ν := lam.restrict (O : Set K)
  haveI : IsProbabilityMeasure ν := ⟨by simpa [ν] using hvol⟩
  let move := fun p : (ι → K) × K => p.1 + p.2 • e
  have hm : Measurable move := (continuous_fst.add (continuous_snd.smul continuous_const)).measurable
  have hp (y : K) : MeasurePreserving (fun x => move (x,y)) μ μ :=
    measurePreserving_add_right μ (y • e)
  have hs (x) (hx : x ∈ W) : (lam D)⁻¹ * lam V ≤ ν {y | move (x,y) ∈ T} := by
    obtain ⟨hxL,hq,hf,hi,hn⟩ := hW hx
    let u := Units.mk0 (slope x) hn
    have hpre : (fun y : K => (u:K)*y+Q x) ⁻¹' D = (O : Set K) := by
      ext y
      change (slope x*y+Q x)/δ ∈ O ↔ y ∈ O
      constructor
      · intro h
        have hy := O.mul_mem hi (O.sub_mem h hq)
        convert hy using 1 <;> field_simp [δ,hreg,hn] <;> ring
      · intro h
        convert O.add_mem (O.mul_mem hf h) hq using 1 <;> ring
    have ha := HaarSlices.affine_slice lam u (Q x) O D hOp.measurableSet hDo.measurableSet hvol hpre hV hVD
    have m₁ : Measurable (fun y : K => (u:K)*y + Q x) := ((continuous_const.mul continuous_id).add continuous_const).measurable
    rw [← ha, Measure.restrict_apply (hV.preimage m₁)]
    change _ ≤ lam.restrict (O : Set K) {y | move (x,y) ∈ T}
    have m₂ : Measurable (fun y : K => move (x,y)) := (continuous_const.add (continuous_id.smul continuous_const)).measurable
    change _ ≤ lam.restrict (O : Set K) ((fun y : K => move (x,y)) ⁻¹' T)
    rw [Measure.restrict_apply (hT.preimage m₂)]
    apply measure_mono
    rintro y ⟨hy,hyO⟩
    refine ⟨⟨fun i _ => O.add_mem (hxL i (mem_univ i)) (O.mul_mem hyO (he i)),?_⟩,hyO⟩
    change Q (x+y • e) ∈ V
    rw [hline]; exact hy
  have hh := HaarSlices.average μ ν T W hT hWo.measurableSet move hm hp ((lam D)⁻¹ * lam V) hs
  have hreal := ENNReal.toReal_mono hTf hh
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv] at hreal
  have exact_set : T = {x | (∀ i, x i ∈ O) ∧ Q x ∈ V} := by
    ext x; simp [T,L,Set.mem_pi]
  rw [exact_set] at hreal
  simpa [c,mul_assoc,μ] using hreal
end CoordinateFloor
#print axioms CoordinateFloor.lower
