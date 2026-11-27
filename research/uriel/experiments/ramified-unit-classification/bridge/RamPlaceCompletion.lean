import RamFieldPlace
import RamFieldMeasure
open UniformSpace Topology NumberField IsDedekindDomain
open scoped RamFieldCompletion NNReal
noncomputable section
namespace RamPlaceCompletion
open RamGlobal (F)
open RamFieldPlace (place vnorm valuation_equiv)
open RamFieldCompletion (incl)
abbrev V := place.adicCompletion F

local instance : IsUltrametricDist F := ⟨fun x y z =>
  IsUltrametricDist.dist_triangle_max (incl x) (incl y) (incl z)⟩
local instance : Valued F ℝ≥0 := NormedField.toValued

def sourceEquiv : WithVal (place.valuation F) ≃ᵤ F :=
  WithVal.uniformEquiv (w:=vnorm) rfl valuation_equiv

def e : V ≃+* RamField.K :=
  ((HeightOneSpectrum.adicCompletion.equiv F place).trans
    (Completion.mapRingEquiv (WithVal.equiv (place.valuation F))
      sourceEquiv.continuous sourceEquiv.symm.continuous)).trans RamFieldCompletion.completionRingEquiv

def u : V ≃ᵤ RamField.K :=
  ((HeightOneSpectrum.adicCompletion.uniformEquiv F place).trans
    (Completion.mapEquiv sourceEquiv)).trans RamFieldCompletion.completionEquiv

theorem continuous_e : Continuous e := u.continuous
theorem continuous_e_symm : Continuous e.symm := u.symm.continuous

theorem on_field (x : F) : e (algebraMap F V x) = incl x := by
  change RamFieldCompletion.completionEquiv (Completion.map sourceEquiv
    ((WithVal.equiv (place.valuation F)).symm x : Completion (WithVal (place.valuation F)))) = _
  rw [Completion.map_coe sourceEquiv.uniformContinuous,RamFieldCompletion.completionEquiv_coe]
  rfl

/-- Both integer sets are clopen. Their equality is determined on the dense
global field, where the equivalence of valuations identifies the two unit balls. -/
theorem integer_preimage : e ⁻¹' RamField.integers = (place.adicCompletionIntegers F : Set V) := by
  let A := e ⁻¹' RamField.integers
  let B := (place.adicCompletionIntegers F : Set V)
  have hA : IsClopen A :=
    ⟨(RamField.integers_compact.isClosed.preimage continuous_e),RamField.integers_open.preimage continuous_e⟩
  have hB : IsClopen B := ⟨Valued.isClosed_valuationSubring _,Valued.isOpen_valuationSubring _⟩
  change A=B
  ext x
  refine (HeightOneSpectrum.denseRange_algebraMap F place).induction_on (p:=fun z => z ∈ A ↔ z ∈ B) x ?_ ?_
  · have hset : {z | z ∈ A ↔ z ∈ B} = A ∩ B ∪ Aᶜ ∩ Bᶜ := by ext z; simp; tauto
    rw [hset]
    exact (hA.1.inter hB.1).union (hA.2.isClosed_compl.inter hB.2.isClosed_compl)
  · intro a
    change e (algebraMap F V a) ∈ RamField.integers ↔ Valued.v (algebraMap F V a) ≤ 1
    rw [on_field,RamField.integers_eq_unit_ball,Metric.mem_closedBall,dist_zero_right]
    change ‖incl a‖ ≤ 1 ↔ Valued.v (a:V) ≤ 1
    rw [place.valuedAdicCompletion_eq_valuation']
    exact (valuation_equiv.le_one_iff_le_one (x:=a)).symm

end RamPlaceCompletion
#print axioms RamPlaceCompletion.on_field
#print axioms RamPlaceCompletion.integer_preimage
