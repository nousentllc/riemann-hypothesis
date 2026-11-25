import RamFieldIntegers
open UniformSpace Topology
noncomputable section
namespace RamFieldCompletion
open RamField

abbrev F := QuadraticAlgebra ℚ 2 0

private instance ratNonsquare : Fact (∀ x:ℚ, x^2 ≠ 2+0*x) := by
  constructor
  intro x hx
  apply RamField.nonsquare.out (algebraMap ℚ ℚ_[2] x)
  simpa only [map_pow,map_add,map_ofNat,map_zero,map_mul] using congrArg (algebraMap ℚ ℚ_[2]) hx

def incl : F →+* K := coeffMap (algebraMap ℚ ℚ_[2])

theorem dense : DenseRange incl := by
  have hp := (Padic.denseRange_ratCast 2).prodMap (Padic.denseRange_ratCast 2)
  have ht := coordinates.toHomeomorph.symm.surjective.denseRange.comp hp
    coordinates.toHomeomorph.symm.continuous
  have heq : Set.range incl = Set.range
    (coordinates.toHomeomorph.symm ∘ Prod.map ((↑) : ℚ → ℚ_[2]) ((↑) : ℚ → ℚ_[2])) := by
    ext x; constructor
    · rintro ⟨y,rfl⟩; exact ⟨(y.re,y.im),rfl⟩
    · rintro ⟨⟨a,b⟩,rfl⟩; exact ⟨⟨a,b⟩,rfl⟩
  change Dense (Set.range incl)
  rw [heq]; exact ht

/-- The norm on the global field is specifically the one induced by the embedding over 2. -/
scoped instance atTwoNorm : NormedField F := NormedField.induced F K incl incl.injective

theorem isometry_incl : Isometry incl := by
  apply Isometry.of_dist_eq
  intro _ _; rfl

def completionPackage : AbstractCompletion F where
  space := K
  coe := incl
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing := isometry_incl.isUniformInducing
  dense := dense

def completionEquiv : Completion F ≃ᵤ K := Completion.cPkg.compareEquiv completionPackage

theorem completionEquiv_coe (x : F) : completionEquiv (x : Completion F) = incl x :=
  Completion.cPkg.compare_coe completionPackage x

/-- The uniform comparison also respects the field operations. -/
def completionRingEquiv : Completion F ≃+* K where
  __ := completionEquiv.toEquiv
  map_mul' := by
    intro x y
    induction x,y using Completion.induction_on₂ with
    | hp =>
      exact isClosed_eq (completionEquiv.continuous.comp (continuous_fst.mul continuous_snd))
        ((completionEquiv.continuous.comp continuous_fst).mul (completionEquiv.continuous.comp continuous_snd))
    | ih a b =>
      change completionEquiv ((a : Completion F)*(b : Completion F)) = completionEquiv _ * completionEquiv _
      rw [← Completion.coe_mul, completionEquiv_coe, completionEquiv_coe, completionEquiv_coe, map_mul]
  map_add' := by
    intro x y
    induction x,y using Completion.induction_on₂ with
    | hp =>
      exact isClosed_eq (completionEquiv.continuous.comp (continuous_fst.add continuous_snd))
        ((completionEquiv.continuous.comp continuous_fst).add (completionEquiv.continuous.comp continuous_snd))
    | ih a b =>
      change completionEquiv ((a : Completion F)+(b : Completion F)) = completionEquiv _ + completionEquiv _
      rw [← Completion.coe_add, completionEquiv_coe, completionEquiv_coe, completionEquiv_coe, map_add]

theorem completionRingEquiv_coe (x : F) : completionRingEquiv (x : Completion F) = incl x :=
  completionEquiv_coe x

end RamFieldCompletion
#print axioms RamFieldCompletion.completionRingEquiv_coe
