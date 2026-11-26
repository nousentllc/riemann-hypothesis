import ReadableFourChart
import GaussianFrame

open New New.Floors Matrix
noncomputable section
namespace ReadableIdentityChart
open ReadableFourChart

def idx : Fin 2 ⊕ Fin 1 → Fin 3 := Sum.elim Fin.castSucc (fun _ => 2)

variable {K : Type} [Field K] [CharZero K]

def M (c : K) := (GaussianFrame.frame c).submatrix id idx
def residual (K : Type) [Field K] : Matrix (Fin 1) (Fin 1) (G K) := fun _ _ => -1

theorem frame_pullback (c : K) (hc : c^2 = -7) :
    (M c)ᴴ * M c = planeSumGram (residual K) := by
  ext a b : 1
  change ((GaussianFrame.frame c)ᴴ * GaussianFrame.frame c) (idx a) (idx b) = _
  rw [GaussianFrame.gram_frame c hc]
  rcases a with a|a <;> rcases b with b|b <;> fin_cases a <;> fin_cases b <;> rfl

theorem gram_original (c z : K) (hc : c^2 = -7)
    (p : (G K × (Fin 1 → G K)) × skewAdjoint (G K)) (hp : IsUnit p.1.1) :
    let s := -(imaginary K 1).val*(imaginary K (4+32*z)).val
    let v := algebraChart (halfTrace K) s (residual K) p
    star ((M c) *ᵥ v) ⬝ᵥ ((M c) *ᵥ v) = hermitian K (4+32*z) := by
  dsimp only
  rw [GaussianFrame.pullback,frame_pullback c hc]
  exact four_chart K z (residual K) (by ext i j : 1; simp [residual,conjTranspose_apply]) p hp

abbrev LocalK := QuadraticAlgebra ℚ_[2] 2 0
instance : Fact (∀ x : ℚ_[2], x^2 ≠ 2+0*x) := by
  constructor; intro x hx
  simp only [zero_mul,add_zero] at hx
  have hv := congrArg Padic.valuation hx
  rw [Padic.valuation_pow,show (2:ℚ_[2]).valuation = 1 from Padic.valuation_p] at hv
  omega

theorem root_exists : ∃ c : LocalK, c^2 = -7 := by
  let F : Polynomial ℤ_[2] := Polynomial.X^2+Polynomial.C 7
  have hnorm : ‖F.aeval (1:ℤ_[2])‖ < ‖F.derivative.aeval (1:ℤ_[2])‖^2 := by
    have hn : ‖(2:ℤ_[2])‖ = 1/2 := by simpa using (PadicInt.norm_p (p:=2))
    have h : ‖(8:ℤ_[2])‖ < ‖(2:ℤ_[2])‖^2 := by
      rw [show (8:ℤ_[2])=2^3 by norm_num,norm_pow,hn]; norm_num
    convert h using 2 <;> norm_num [F,Polynomial.derivative_pow]
  obtain ⟨a,ha,-⟩ := hensels_lemma hnorm
  have hh : a^2+7=0 := by simpa [F] using ha
  let f : ℤ_[2] →+* LocalK := (algebraMap ℚ_[2] LocalK).comp PadicInt.Coe.ringHom
  refine ⟨f a,?_⟩
  have hz := congrArg f hh
  simp only [map_add,map_pow,map_ofNat,map_zero] at hz
  exact eq_neg_of_add_eq_zero_left hz

set_option maxHeartbeats 2400000 in
theorem realized :
    ∃ c : LocalK, c^2 = -7 ∧ ∀ (z : LocalK)
      (p : (G LocalK × (Fin 1 → G LocalK)) × skewAdjoint (G LocalK)), IsUnit p.1.1 →
      let s := -(imaginary LocalK 1).val*(imaginary LocalK (4+32*z)).val
      let x := M c *ᵥ algebraChart (halfTrace LocalK) s (residual LocalK) p
      star x ⬝ᵥ x = hermitian LocalK (4+32*z) := by
  obtain ⟨c,h⟩ := root_exists
  exact ⟨c,h,fun z p hp => @gram_original LocalK _ _ c z h p hp⟩

end ReadableIdentityChart
#print axioms ReadableIdentityChart.frame_pullback
#print axioms ReadableIdentityChart.realized
