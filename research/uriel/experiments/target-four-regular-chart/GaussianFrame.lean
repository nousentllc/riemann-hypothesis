import Mathlib

open Matrix
noncomputable section
namespace GaussianFrame
variable {K : Type} [Field K] [CharZero K]
abbrev G (K : Type) [Field K] := QuadraticAlgebra K (-1) 0

/-- Columns e, f, z in the original Gaussian coordinates. -/
def frame (c : K) : Matrix (Fin 3) (Fin 3) (G K) :=
  fun
    | 0,0 => ⟨1,0⟩
    | 0,1 => ⟨1/2,0⟩
    | 0,2 => ⟨0,0⟩
    | 1,0 => ⟨1,1⟩
    | 1,1 => ⟨-1/2,-1/2⟩
    | 1,2 => ⟨c,-2⟩
    | 2,0 => ⟨c,2⟩
    | 2,1 => ⟨-c/2,-1⟩
    | 2,2 => ⟨-1,1⟩

def plane (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) (G K) :=
  !![0,1,0;1,0,0;0,0,-1]

local macro "frame_entry" : tactic => `(tactic|
  (apply QuadraticAlgebra.ext <;>
   norm_num [frame,plane,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ,
     QuadraticAlgebra.re_star,QuadraticAlgebra.im_star,QuadraticAlgebra.re_mul,
     QuadraticAlgebra.im_mul,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,
     QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero] <;> try ring_nf))

theorem gram_frame (c : K) (hc : c^2 = -7) : (frame c)ᴴ * frame c = plane K := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> frame_entry <;>
    try simp only [hc,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat] <;> ring

theorem det_frame (c : K) (hc : c^2 = -7) : (frame c).det = -1 := by
  rw [Matrix.det_fin_three]
  frame_entry <;> try simp only [hc] <;> ring

theorem central_vector (c : K) :
    frame c *ᵥ (![1,2,0] : Fin 3 → G K) = ![2,0,0] := by
  ext i : 1
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> frame_entry <;>
    simp only [QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat] <;> ring

theorem pullback {I J : Type} [Fintype I] [Fintype J]
    (M : Matrix I J (G K)) (v : J → G K) :
    star (M *ᵥ v) ⬝ᵥ (M *ᵥ v) = star v ⬝ᵥ ((Mᴴ * M) *ᵥ v) := by
  rw [←Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec (star v) Mᴴ,Matrix.star_mulVec]

end GaussianFrame
#print axioms GaussianFrame.gram_frame
#print axioms GaussianFrame.det_frame
#print axioms GaussianFrame.central_vector
#print axioms GaussianFrame.pullback
