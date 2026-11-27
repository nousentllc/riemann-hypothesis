import RamField
import GaussianTrace

open NumberField HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW
open scoped Matrix TensorProduct
noncomputable section
namespace RamGlobal
abbrev F := QuadraticAlgebra ℚ 2 0
instance irredF : Fact (∀ x : ℚ, x^2 ≠ 2+0*x) := by
  constructor
  intro x h
  apply RamField.nonsquare.out (algebraMap ℚ ℚ_[2] x)
  simpa only [map_pow,map_add,map_ofNat,map_zero,map_mul] using congrArg (algebraMap ℚ ℚ_[2]) h
instance : NumberField F := {}
instance : Algebra F RamField.K := (RamField.coeffMap (algebraMap ℚ ℚ_[2])).toAlgebra

def realEmbedding : F →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨Real.sqrt 2, by
    simp [Rat.smul_def,←sq,Real.sq_sqrt]⟩

theorem root_sq : (QuadraticAlgebra.omega : F)^2=2 := by
  rw [pow_two,QuadraticAlgebra.omega_mul_omega_eq_mk]
  rfl

theorem fixed (f : F →+* ℂ) (x : F) : star (f x)=f x := by
  have hs : (f QuadraticAlgebra.omega)^2 = (2:ℂ) := by rw [←map_pow,root_sq,map_ofNat]
  have ht : ((Real.sqrt 2 : ℝ) : ℂ)^2=(2:ℂ) := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hd := sq_eq_sq_iff_eq_or_eq_neg.mp (hs.trans ht.symm)
  have hfix : star (f QuadraticAlgebra.omega) = f QuadraticAlgebra.omega := by
    rcases hd with h|h <;> rw [h] <;> simp
  obtain ⟨a,b⟩ := x
  rw [QuadraticAlgebra.mk_eq_add_smul_omega,Algebra.smul_def]
  change star (f (algebraMap ℚ F a + algebraMap ℚ F b * QuadraticAlgebra.omega)) = _
  simp [hfix]

instance realF : IsTotallyReal F where
  isReal v := by
    rw [InfinitePlace.isReal_iff,ComplexEmbedding.isReal_iff]
    ext x
    exact fixed v.embedding x

abbrev E := QuadraticAlgebra F (-1) 0
instance irredE : Fact (∀ x : F, x^2 ≠ -1+0*x) := by
  constructor
  intro x h
  have hr := congrArg realEmbedding h
  simp only [map_pow,map_neg,map_one,zero_mul,add_zero] at hr
  nlinarith [sq_nonneg (realEmbedding x)]
instance : NumberField E := by
  have : FiniteDimensional ℚ E := Module.Finite.trans F E
  exact {}

def conjG : E →ₐ[F] E := { starRingEnd E with
  commutes' x := by
    change star (⟨x,0⟩ : E) = ⟨x,0⟩
    rw [QuadraticAlgebra.star_mk]; simp }
abbrev ii : E := QuadraticAlgebra.omega
theorem ii_sq : ii^2=(-1:E) := by rw [pow_two,QuadraticAlgebra.omega_mul_omega_eq_mk]; rfl

theorem isCM : IsCMExt F E conjG := by
  refine ⟨inferInstance,⟨fun v => InfinitePlace.not_isReal_iff_isComplex.mp fun hv => ?_⟩,
    QuadraticAlgebra.finrank_eq_two _ _,?_⟩
  · let f := InfinitePlace.embedding_of_isReal hv
    have h := congrArg f ii_sq
    simp only [map_pow,map_neg,map_one] at h
    nlinarith [sq_nonneg (f ii)]
  · intro τ x
    have hi : (τ ii)^2=(-1 : ℂ) := by rw [←map_pow,ii_sq,map_neg,map_one]
    have hI : τ ii = Complex.I ∨ τ ii = -Complex.I :=
      sq_eq_sq_iff_eq_or_eq_neg.mp (hi.trans Complex.I_sq.symm)
    have hc : star (τ ii) = -τ ii := by rcases hI with h|h <;> rw [h] <;> simp
    have hF (c:F) : star (τ (algebraMap F E c))=τ (algebraMap F E c) :=
      fixed (τ.comp (algebraMap F E)) c
    obtain ⟨a,b⟩ := x
    change τ (star (⟨a,b⟩ : E)) = _
    have hs : star (⟨a,b⟩ : E) = ⟨a,-b⟩ := by ext <;> simp
    rw [hs,QuadraticAlgebra.mk_eq_add_smul_omega,QuadraticAlgebra.mk_eq_add_smul_omega a b,
      Algebra.smul_def,Algebra.smul_def]
    change τ (algebraMap F E a + algebraMap F E (-b) * ii) = star (τ (algebraMap F E a + algebraMap F E b * ii))
    simp [hc,hF]

theorem herm_id : IsHermND conjG (1 : Matrix (Fin 3) (Fin 3) E) := by
  constructor
  · intro i j; by_cases h : i=j <;> simp [Matrix.one_apply,h,Ne.symm]
  · simp
abbrev gb := QuadraticAlgebra.basis (-1 : F) 0
theorem gb_zero : gb 0 = (1 : E) :=
  gb.repr.injective (by ext1 j; fin_cases j <;> simp [gb,QuadraticAlgebra.basis_repr_apply] <;> rfl)
theorem gb_one : gb 1 = ii :=
  gb.repr.injective (by ext1 j; fin_cases j <;> simp [gb,ii,QuadraticAlgebra.basis_repr_apply])
theorem trace_i : Algebra.trace F E ii = 0 := by
  have h := TraceFormGram.trace_sig isCM ii
  have hs : conjG ii = -ii := by change star ii = -ii; ext <;> simp [ii,QuadraticAlgebra.re_star,QuadraticAlgebra.im_star]
  rw [hs,map_neg] at h
  exact (mul_eq_zero.mp (show (2:F)*Algebra.trace F E ii=0 by linear_combination -h)).resolve_left (by norm_num)
theorem gram_matrix : TraceFormGram.trGram conjG (1 : Matrix (Fin 3) (Fin 3) E) gb =
    (2 : F) • (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) F) := by
  ext1 ⟨i,k⟩ ⟨j,l⟩
  by_cases he : i=j
  · subst j
    have hs : conjG ii = -ii := by change star ii = -ii; ext <;> simp [ii,QuadraticAlgebra.re_star,QuadraticAlgebra.im_star]
    have htr : Algebra.trace F E (1 : E) = 2 := by
      have h := Algebra.trace_algebraMap (R := F) (S := E) (1 : F)
      simpa [QuadraticAlgebra.finrank_eq_two] using h
    fin_cases k <;> fin_cases l <;>
      simp [TraceFormGram.trGram, Matrix.one_apply,gb_zero,gb_one,hs,trace_i,htr,
        ← pow_two,ii_sq,Matrix.smul_apply]
  · simp [TraceFormGram.trGram,Matrix.one_apply,he,Matrix.smul_apply]

end RamGlobal
#print axioms RamGlobal.isCM
#print axioms RamGlobal.gram_matrix
