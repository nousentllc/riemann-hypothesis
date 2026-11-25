import GaussianField
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EtaleAwayQuotientEqLocalization
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW
open scoped TensorProduct Matrix
noncomputable section
namespace TargetOne
abbrev gb := QuadraticAlgebra.basis (-1 : ℚ) 0
theorem gb_zero : gb 0 = (1 : E) :=
  gb.repr.injective (by ext j; fin_cases j <;> simp [gb,QuadraticAlgebra.basis_repr_apply] <;> rfl)
theorem gb_one : gb 1 = ii :=
  gb.repr.injective (by ext j; fin_cases j <;> simp [gb,ii,QuadraticAlgebra.basis_repr_apply])
theorem trace_i : Algebra.trace ℚ E ii = 0 := by
  have h := TraceFormGram.trace_sig isCM ii
  have hs : conjG ii = -ii := by change star ii = -ii; ext <;> simp [ii,QuadraticAlgebra.re_star,QuadraticAlgebra.im_star]
  rw [hs,map_neg] at h
  linarith
theorem gram_matrix : TraceFormGram.trGram conjG (1 : Matrix (Fin 3) (Fin 3) E) gb =
    (2 : ℚ) • (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℚ) := by
  ext ⟨i,k⟩ ⟨j,l⟩
  by_cases he : i=j
  · subst j
    have hs : conjG ii = -ii := by change star ii = -ii; ext <;> simp [ii,QuadraticAlgebra.re_star,QuadraticAlgebra.im_star]
    have htr : Algebra.trace ℚ E (1 : E) = 2 := by
      have h := Algebra.trace_algebraMap (R := ℚ) (S := E) (1 : ℚ)
      simpa [QuadraticAlgebra.finrank_eq_two] using h
    fin_cases k <;> fin_cases l <;>
      simp [TraceFormGram.trGram, Matrix.one_apply,gb_zero,gb_one,hs,trace_i,htr,
        ← pow_two,ii_sq,Matrix.smul_apply]
  · simp [TraceFormGram.trGram,Matrix.one_apply,he,Matrix.smul_apply]
theorem trace_coords (R : Type) [CommRing R] [Algebra ℚ R] (x y : Fin 3 → R ⊗[ℚ] E) :
    Algebra.trace R (R ⊗[ℚ] E) (hR R conjG (1 : Matrix (Fin 3) (Fin 3) E) x y) =
      (fun p : Fin 3 × Fin 2 => (Algebra.TensorProduct.basis R gb).repr (x p.1) p.2) ⬝ᵥ
        (((2 : R) • (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) R)) *ᵥ
          fun p : Fin 3 × Fin 2 => (Algebra.TensorProduct.basis R gb).repr (y p.1) p.2) := by
  let J := (1 : Matrix (Fin 3) (Fin 3) E)
  have hB : (TraceFormGram.trGram conjG J gb).map (algebraMap ℚ R) =
      (2:R) • (1 : Matrix _ _ R) := by
    rw [show J=1 from rfl,gram_matrix]
    ext i j; by_cases h : i=j <;> simp [Matrix.map_apply,Matrix.one_apply,Matrix.smul_apply,h] <;> exact map_ofNat _ _
  rw [← hB]
  have hh : hR R conjG J x y = ∑ i, ∑ j, sigR R conjG (x i) * ((1 : R) ⊗ₜ[ℚ] J i j) * y j := rfl
  change Algebra.trace R (R ⊗[ℚ] E) (hR R conjG J x y) = _
  rw [hh]
  simp only [map_sum,TraceFormGram.trace_entry conjG gb R,dotProduct,Matrix.mulVec,
    Fintype.sum_prod_type,Matrix.map_apply,TraceFormGram.trGram,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
end TargetOne
#print axioms TargetOne.trace_coords
