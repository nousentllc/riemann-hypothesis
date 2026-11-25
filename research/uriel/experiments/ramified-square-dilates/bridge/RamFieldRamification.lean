import RamFieldPlace
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
open NumberField IsDedekindDomain
noncomputable section
namespace RamFieldPlace
open RamGlobal (F)

def rootIntegral : 𝓞 F := ⟨QuadraticAlgebra.omega, by
  apply IsIntegral.of_pow (n:=2) (by decide)
  rw [RamGlobal.root_sq]
  exact (show IsIntegral ℤ (algebraMap ℤ F 2) from isIntegral_algebraMap)⟩

theorem rootIntegral_sq : rootIntegral ^ 2 = (2:𝓞 F) :=
  Subtype.ext RamGlobal.root_sq

def rootIdeal : Ideal (𝓞 F) := Ideal.span {rootIntegral}

theorem rootIdeal_sq : rootIdeal ^ 2 = Ideal.span {(2:𝓞 F)} := by
  rw [rootIdeal,Ideal.span_singleton_pow,rootIntegral_sq]

theorem rootIdeal_norm : rootIdeal.absNorm = 2 := by
  have h := congrArg Ideal.absNorm rootIdeal_sq
  rw [map_pow,show (2:𝓞 F) = ((2:ℕ):𝓞 F) by rfl, Ideal.absNorm_span_natCast, RingOfIntegers.rank,
    QuadraticAlgebra.finrank_eq_two] at h
  nlinarith

private theorem rootIdeal_max : rootIdeal.IsMaximal := by
  have hp : rootIdeal.IsPrime := Ideal.isPrime_of_irreducible_absNorm
    (by rw [rootIdeal_norm]; exact Nat.prime_two)
  apply hp.isMaximal
  intro h
  have hn := rootIdeal_norm
  rw [h,Ideal.absNorm_bot] at hn
  contradiction

theorem eq_rootIdeal {p : HeightOneSpectrum (𝓞 F)} (h : (2:𝓞 F) ∈ p.asIdeal) :
    rootIdeal = p.asIdeal := by
  apply rootIdeal_max.eq_of_le p.isPrime.ne_top
  apply (Ideal.span_singleton_le_iff_mem p.asIdeal).mpr
  apply p.isPrime.mem_of_pow_mem 2
  simpa [rootIntegral_sq] using h

theorem unique_above_two (p : HeightOneSpectrum (𝓞 F)) (h : (2:𝓞 F) ∈ p.asIdeal) : p=place :=
  HeightOneSpectrum.ext ((eq_rootIdeal h).symm.trans (eq_rootIdeal two_mem))

theorem factorization : place.asIdeal^2 = Ideal.span {(2:𝓞 F)} := by
  rw [←eq_rootIdeal two_mem]; exact rootIdeal_sq

theorem residue_card : Nat.card ((𝓞 F) ⧸ place.asIdeal) = 2 := by
  rw [← eq_rootIdeal two_mem]
  exact rootIdeal_norm

end RamFieldPlace
#print axioms RamFieldPlace.unique_above_two
#print axioms RamFieldPlace.factorization
#print axioms RamFieldPlace.residue_card
