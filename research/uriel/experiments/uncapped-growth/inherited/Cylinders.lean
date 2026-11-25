import AllDepth
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
open MeasureTheory NumberField IsDedekindDomain Topology
open scoped ENNReal
noncomputable section
namespace TargetOne
abbrev primeTwo : Nat.Primes := ⟨2,Nat.prime_two⟩
abbrev placeTwo := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm primeTwo
abbrev K := placeTwo.adicCompletion ℚ
instance : MeasurableSpace K := borel K
instance : BorelSpace K := ⟨rfl⟩
abbrev O := placeTwo.adicCompletionIntegers ℚ
abbrev ei := PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) primeTwo
abbrev ef := Padic.adicCompletionEquiv (𝓞 ℚ) primeTwo
abbrev inc : ℤ_[2] →+* K := O.subtype.comp ei.toRingEquiv.toRingHom
def digit (r : ℕ) := PadicInt.toZModPow (p := 2) r
def cylinder (r : ℕ) (b : ZMod (2^r)) : Set K := inc '' {x | digit r x = b}
theorem digit_nat (r : ℕ) (b : ZMod (2^r)) : digit r (b.val : ℤ_[2]) = b := by simp [digit]
theorem ball_digit (r : ℕ) (a : ℤ_[2]) :
    {x | digit r x = digit r a} = Metric.closedBall a ((2:ℝ)^(-(r:ℤ))) := by
  ext x
  have hh := PadicInt.norm_le_pow_iff_mem_span_pow (p := 2) (x-a) r
  norm_num only [Nat.cast_ofNat] at hh
  have hker := PadicInt.ker_toZModPow (p := 2) r
  norm_num only [Nat.cast_ofNat] at hker
  rw [Metric.mem_closedBall, dist_eq_norm, hh,
    ← hker, RingHom.mem_ker, map_sub, sub_eq_zero]
  rfl
theorem compact_cylinder (r : ℕ) (b : ZMod (2^r)) : IsCompact (cylinder r b) := by
  have hs : {x | digit r x = b} = Metric.closedBall (b.val : ℤ_[2]) ((2:ℝ)^(-(r:ℤ))) := by rw [← ball_digit,digit_nat]
  rw [cylinder,hs]
  exact (Metric.isClosed_closedBall.isCompact).image (continuous_subtype_val.comp ei.continuous)
theorem open_cylinder (r : ℕ) (b : ZMod (2^r)) : IsOpen (cylinder r b) := by
  have hs : {x | digit r x = b} = Metric.closedBall (b.val : ℤ_[2]) ((2:ℝ)^(-(r:ℤ))) := by rw [← ball_digit,digit_nat]
  rw [cylinder,hs]
  have h := (IsUltrametricDist.isOpen_closedBall (b.val : ℤ_[2]) (by positivity : (2:ℝ)^(-(r:ℤ)) ≠ 0))
  change IsOpen ((Subtype.val ∘ ei) '' _)
  rw [Set.image_comp]
  exact (Valued.isOpen_valuationSubring _).isOpenEmbedding_subtypeVal.isOpenMap _
    (ei.toHomeomorph.isOpenMap _ h)
theorem disjoint_cyl (r : ℕ) : Pairwise (fun a b => Disjoint (cylinder r a) (cylinder r b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,h⟩
  have : y=x := ei.injective (Subtype.coe_injective h)
  exact hab (hx.symm.trans (this ▸ hy))
theorem union_cyl (r : ℕ) : ⋃ b, cylinder r b = (O : Set K) := by
  ext x
  constructor
  · rintro ⟨_,⟨b,rfl⟩,y,_,rfl⟩
    exact (ei y).2
  · intro hx
    obtain ⟨y,hy⟩ := ei.surjective ⟨x,hx⟩
    exact Set.mem_iUnion.mpr ⟨digit r y,y,rfl,congrArg Subtype.val hy⟩
theorem cyl_mass (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam (O : Set K)=1)
    (r : ℕ) (b : ZMod (2^r)) : lam (cylinder r b)=1/(2^r : ℝ≥0∞) := by
  have meas (t : ZMod (2^r)) : MeasurableSet (cylinder r t) := (open_cylinder r t).measurableSet
  have flat (t : ZMod (2^r)) : lam (cylinder r t)=lam (cylinder r b) := by
    let z : ℤ_[2] := ((b-t).val : ℤ_[2])
    have hz : digit r z=b-t := digit_nat r _
    have pre : (fun x : K => inc z + x) ⁻¹' cylinder r b = cylinder r t := by
      ext x
      constructor
      · rintro ⟨y,hy,h⟩
        refine ⟨y-z,?_,?_⟩
        · change digit r (y-z) = t
          rw [map_sub,show digit r y=b from hy,hz]; ring
        · rw [map_sub,h]; exact add_sub_cancel_left _ _
      · rintro ⟨y,hy,rfl⟩
        refine ⟨z+y,?_,map_add ..⟩
        change digit r (z+y)=b
        rw [map_add,hz,show digit r y=t from hy]; ring
    rw [← pre,measure_preimage_add]
  have h := measure_iUnion (μ := lam) (disjoint_cyl r) meas
  rw [union_cyl,hvol,tsum_fintype] at h
  rw [Finset.sum_congr rfl (fun t _ => flat t)] at h
  simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] at h
  exact (ENNReal.eq_div_iff (by positivity) (by finiteness)).mpr h.symm
end TargetOne
