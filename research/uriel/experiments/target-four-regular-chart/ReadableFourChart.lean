import Lib.General.Measure.QuadricDisintegration

/-! The algebraic chart extracted from the pinned readable-edition definition.
The unrestricted source lemma is used in the definitional comparison. Its
integral-place specialization and its Fourier inputs are unnecessary here. -/

open Matrix MeasureTheory Sum Ring Units Function Set
open New New.Floors
noncomputable section

namespace ReadableFourChart

variable {A : Type} [CommRing A] [StarRing A] {I : Type} [Fintype I]

/-- Here s is the Hermitian target, written as the inverse skew unit times the
readable label. This formula has no Place or IntegralPlace argument. -/
def algebraChart (τ s : A) (T : Matrix I I A)
    (p : (A × (I → A)) × skewAdjoint A) : Fin 2 ⊕ I → A :=
  let ((t,w),a) := p
  ![(star t)⁻¹ʳ * τ * (s - star w ⬝ᵥ T *ᵥ w) + t * a, t] ⊕ᵥ w

theorem literal [TopologicalSpace A] [MeasureSpace A] [P : Place A] (T : Matrix I I A)
    (b : skewAdjoint A) :
    Place.flatChart T b = algebraChart P.element (P.skewUnit⁻¹.val * b.val) T := rfl

/-- Direct specialization of the source calculation to its algebraic hypotheses. -/
theorem form (τ s : A) (hτ : τ + star τ = 1) (hs : star s=s) (T : Matrix I I A)
    (hT : Tᴴ=T) (p : (A × (I → A)) × skewAdjoint A) (hp : IsUnit p.1.1) :
    star (algebraChart τ s T p) ⬝ᵥ planeSumGram T *ᵥ algebraChart τ s T p = s := by
  obtain ⟨⟨t,w⟩,a⟩ := p
  let q : A := star w ⬝ᵥ T *ᵥ w
  suffices ((star t)⁻¹ʳ * τ * (s-q)+t*a)*star t +
      t*(t⁻¹ʳ*star τ*(s-q)-star t*a)+q=s by
    simpa [algebraChart,fromBlocks_mulVec,star_sumElim,inverse_star,
      star_dotProduct_mulVec_comm hT w w,hs,←sub_eq_add_neg]
  linear_combination (s-q)*(τ*inverse_mul_cancel (star t) hp.star +
    star τ*inverse_mul_cancel t hp+hτ)

section Gaussian
variable (K : Type) [Field K] [CharZero K]
abbrev G := QuadraticAlgebra K (-1) 0
def imaginary (t : K) : skewAdjoint (G K) :=
  ⟨⟨0,t⟩,by ext <;> simp⟩
def hermitian (s : K) : G K := ⟨s,0⟩
def halfTrace : G K := ⟨1/2,0⟩

theorem half_trace : halfTrace K + star (halfTrace K) = 1 := by
  ext <;> simp [halfTrace,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one] <;> ring

theorem target_decode (s : K) :
    -(imaginary K 1).val*(imaginary K s).val=hermitian K s := by
  ext <;> simp [imaginary,hermitian,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]

theorem four_chart (z : K) (T : Matrix I I (G K)) (hT : Tᴴ=T)
    (p : (G K × (I → G K)) × skewAdjoint (G K)) (hp : IsUnit p.1.1) :
    let s := -(imaginary K 1).val*(imaginary K (4+32*z)).val
    star (algebraChart (halfTrace K) s T p) ⬝ᵥ planeSumGram T *ᵥ
      algebraChart (halfTrace K) s T p = hermitian K (4+32*z) := by
  dsimp only
  rw [target_decode]
  apply form _ _ (half_trace K) _ _ hT _ hp
  ext <;> simp [hermitian]

end Gaussian
end ReadableFourChart
#print axioms ReadableFourChart.literal
#print axioms ReadableFourChart.form
#print axioms ReadableFourChart.four_chart
