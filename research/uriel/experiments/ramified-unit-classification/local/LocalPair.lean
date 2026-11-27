import Mathlib

open scoped Matrix
noncomputable section
namespace LocalPair

variable {K I : Type*} [Field K] [CharZero K] [Fintype I] [DecidableEq I]

def quad (B : Matrix I I K) (x : I → K) : K := (2:K)⁻¹ * (x ⬝ᵥ (B *ᵥ x))

/-- The coefficient along a zero direction is exactly the linear polar pairing;
the vanishing quadratic coefficient is the entire reason averaging works. -/
theorem along (B : Matrix I I K) (hB : B.IsSymm) (e : I → K)
    (he : e ⬝ᵥ (B *ᵥ e) = 0) (w : I → K) (y : K) :
    quad B (w + y • e) = quad B w + y * (w ⬝ᵥ (B *ᵥ e)) := by
  let b := B.toBilin'
  have bs : b e w = b w e := (Matrix.isSymm_toBilin'_iff_isSymm.mpr hB).eq _ _
  have be : b e e = 0 := by simpa [b, Matrix.toBilin'_apply'] using he
  have hb (v z : I → K) : v ⬝ᵥ (B *ᵥ z) = b v z := (Matrix.toBilin'_apply' ..).symm
  unfold quad
  simp only [hb, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, bs, be]
  ring

/-- Given one nonzero isotropic vector and a nonzero covector, perform the full
hyperbolic correction, producing a second null vector with pairing exactly one. -/
theorem partner (B : Matrix I I K) (hB : B.IsSymm) (e : I → K)
    (he : e ⬝ᵥ (B *ᵥ e) = 0) (hder : B *ᵥ e ≠ 0) :
    ∃ f : I → K, quad B f = 0 ∧ f ⬝ᵥ (B *ᵥ e) = 1 ∧
      ∀ (w : I → K) (y : K), quad B (w + y • e) = quad B w + y * (w ⬝ᵥ (B *ᵥ e)) := by
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hder
  change (B *ᵥ e) j ≠ 0 at hj
  let z : I → K := Pi.single j ((B *ᵥ e) j)⁻¹
  have hz : z ⬝ᵥ (B *ᵥ e) = 1 := by
    simp [z, hj]
  let f := z + (-quad B z) • e
  refine ⟨f, ?_, ?_, along B hB e he⟩
  · rw [show f = _ from rfl, along B hB e he, hz]
    ring
  · simp [f, add_dotProduct, smul_dotProduct, he, hz]

end LocalPair
#print axioms LocalPair.partner
