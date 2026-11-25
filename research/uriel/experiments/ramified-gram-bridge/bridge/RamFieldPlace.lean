import RamFieldCompletion
import RamGlobal
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
open UniformSpace Topology NumberField IsDedekindDomain
open scoped NNReal
noncomputable section
namespace RamFieldPlace
open RamGlobal (F)
open RamFieldCompletion (incl)

abbrev vnorm : Valuation F ℝ≥0 := (NormedField.valuation (K:=RamField.K)).comap incl
abbrev A := vnorm.valuationSubring

theorem integral_mem (x : 𝓞 F) : (x:F) ∈ A := by
  have hi : IsIntegral A (x:F) := (show IsIntegral ℤ (x:F) from x.2).tower_top
  obtain ⟨y,hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  exact hy ▸ y.2

def integralMap : 𝓞 F →+* A :=
  (algebraMap (𝓞 F) F).codRestrict A.toSubring integral_mem

def centerIdeal : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal A).comap integralMap

theorem mem_center (x:𝓞 F) : x ∈ centerIdeal ↔ vnorm (x:F)<1 :=
  Valuation.mem_maximalIdeal_iff F vnorm

theorem value_two : vnorm (2:F) = 1/2 := by
  apply NNReal.eq
  change ‖incl (2:F)‖ = (↑(1/2:ℝ≥0):ℝ)
  rw [map_ofNat, ← map_ofNat (algebraMap ℚ_[2] RamField.K) 2, norm_algebraMap']
  simpa using (Padic.norm_p (p:=2))

theorem two_mem : (2:𝓞 F) ∈ centerIdeal := by
  rw [mem_center]
  change vnorm (2:F)<1
  rw [value_two]; norm_num

def place : HeightOneSpectrum (𝓞 F) where
  asIdeal := centerIdeal
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by intro h; have hh := two_mem; rw [h,Ideal.mem_bot] at hh; norm_num at hh

theorem algebraMap_val (x : 𝓞 F) : vnorm (algebraMap (𝓞 F) F x) ≤ 1 := integral_mem x

theorem valuation_equiv : (place.valuation F).IsEquiv vnorm := by
  rw [Valuation.isEquiv_iff_valuationSubring,←HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  apply ValuationSubring.eq_of_le_of_ne_top
  · rintro x ⟨a,s,hs,rfl⟩
    have hno : ¬ vnorm (s:F) < 1 := fun h => hs ((mem_center s).mpr h)
    have hsone := le_antisymm (algebraMap_val s) (not_lt.mp hno)
    change vnorm ((algebraMap (𝓞 F) F a) * (algebraMap (𝓞 F) F s)⁻¹) ≤ 1
    rw [map_mul,map_inv₀,hsone,inv_one,mul_one]; exact algebraMap_val _
  · intro h
    have htwo : (2:F)⁻¹ ∈ A := by change _ ∈ vnorm.valuationSubring; rw [h]; trivial
    change vnorm ((2:F)⁻¹) ≤ 1 at htwo
    rw [map_inv₀,value_two] at htwo
    norm_num at htwo

end RamFieldPlace
#print axioms RamFieldPlace.valuation_equiv
