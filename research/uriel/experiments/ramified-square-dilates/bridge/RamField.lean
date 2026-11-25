import DyadicLocal
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

open MeasureTheory Topology HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW
open scoped ENNReal
noncomputable section
namespace RamField

abbrev K := QuadraticAlgebra ℚ_[2] 2 0
abbrev O := QuadraticAlgebra ℤ_[2] 2 0
abbrev R (k : ℕ) := QuadraticAlgebra (ZMod (2^k)) 2 0

instance nonsquare : Fact (∀ x : ℚ_[2], x^2 ≠ 2 + 0*x) := by
  constructor
  intro x hx
  simp only [zero_mul, add_zero] at hx
  have h := congrArg Padic.valuation hx
  rw [Padic.valuation_pow] at h
  have hp : (2 : ℚ_[2]).valuation = 1 := Padic.valuation_p
  rw [hp] at h
  omega

instance : NontriviallyNormedField K := spectralNorm.nontriviallyNormedField ℚ_[2] K
instance : NormedAlgebra ℚ_[2] K := spectralNorm.normedAlgebra ℚ_[2] K
instance : IsUltrametricDist K := IsUltrametricDist.of_normedAlgebra ℚ_[2]
instance : ProperSpace K := FiniteDimensional.proper ℚ_[2] K
instance : MeasurableSpace K := borel K
instance : BorelSpace K := ⟨rfl⟩

theorem locally : IsLocR K :=
  TargetOne.isLocR_of_ultrametric K (by
    intro h
    have hh := congrArg QuadraticAlgebra.re h
    change (2 : ℚ_[2]) = 0 at hh
    norm_num at hh)

def coeffMap {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) :
    QuadraticAlgebra S 2 0 →+* QuadraticAlgebra T 2 0 where
  toFun x := ⟨f x.re, f x.im⟩
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp [map_ofNat]
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

def inc : O →+* K := coeffMap PadicInt.Coe.ringHom
def digit (k : ℕ) : O →+* R k := coeffMap (PadicInt.toZModPow k)

theorem inc_injective : Function.Injective inc := by
  intro x y h
  exact QuadraticAlgebra.ext (Subtype.coe_injective (congrArg QuadraticAlgebra.re h))
    (Subtype.coe_injective (congrArg QuadraticAlgebra.im h))

theorem digit_surjective (k : ℕ) : Function.Surjective (digit k) := by
  intro x
  obtain ⟨a,ha⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow (p:=2) k) x.re
  obtain ⟨b,hb⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow (p:=2) k) x.im
  exact ⟨⟨a,b⟩, QuadraticAlgebra.ext ha hb⟩

def integers : Set K := Set.range inc
def cylinder (k : ℕ) (b : R k) : Set K := inc '' {x | digit k x = b}

def coordinates : K ≃L[ℚ_[2]] (ℚ_[2] × ℚ_[2]) :=
  (show K ≃ₗ[ℚ_[2]] (ℚ_[2] × ℚ_[2]) from
    { QuadraticAlgebra.equivProd 2 0 with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearEquiv

theorem coord_inc (x : O) : coordinates (inc x) = ((x.re : ℚ_[2]), (x.im : ℚ_[2])) := rfl
end RamField
