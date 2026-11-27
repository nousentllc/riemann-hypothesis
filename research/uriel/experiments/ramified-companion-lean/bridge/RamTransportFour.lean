import RamTransportBoxes
import RamFieldMeasure

open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW Topology
open scoped ENNReal

noncomputable section
namespace RamTransportFour

open RamField

abbrev admissibleCount := ∀ k : ℕ, 128 * TargetOne.count 6 (4 : R (k+5)) =
  257 * ((2^(k+5))^2)^5

/-- Every fine target cell has the required *ambient* tube mass before invoking
the original local Gram disintegration. -/
theorem tube_four (hcount : admissibleCount) (lam : Measure K) [lam.IsAddHaarMeasure]
    (hvol : lam integers = 1) (k : ℕ) :
    (Measure.pi fun _ : TargetOne.Idx => lam)
      (RamTransport.tube K integers (cylinder (k+5) 4)) =
      (257/128 : ℝ≥0∞) * lam (cylinder (k+5) 4) := by
  classical
  obtain ⟨i1,i2,i3,i4,-⟩ := id locally
  let : Fintype (R (k+5)) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  let q := (2^(k+5) : ℕ)^2
  have hm (b : R (k+5)) : lam (RamTransport.residueCell inc (digit (k+5)) b) = 1/(q:ℝ≥0∞) := by
    change lam (cylinder (k+5) b) = _
    simpa only [q,Nat.cast_pow,Nat.cast_ofNat] using cyl_mass lam hvol (k+5) b
  have hm' (b : R (k+5)) : MeasurableSet (RamTransport.residueCell inc (digit (k+5)) b) :=
    (open_cylinder (k+5) b).measurableSet
  exact (RamTransport.fiber_count_to_tube inc inc_injective (digit (k+5)) lam hm' _ hm 4).trans
    ((RamTransport.scaled_ratio _ q (by dsimp [q]; positivity) (hcount k)).trans
      (congrArg (_ * ·) (hm 4).symm))

/-- Quantifies over the original disintegrating family; the ratio is independent
of the choice made by the original existence theorem. -/
theorem original_mass (hcount : admissibleCount) (lam : Measure K) (hlam : lam.IsAddHaarMeasure)
    (hvol : lam integers = 1) (m : RamTransport.H K → Measure (RamTransport.W K))
    (hm : RamTransport.family K lam m) :
    m (hermScal K TargetOne.conjG 4) (RamTransport.lattice K integers) = (257/128 : ℝ≥0∞) := by
  let := hlam
  apply RamTransport.original_mass K locally integers integers_compact integers_open lam hlam m hm
    4 (by norm_num) (257/128) (by norm_num [ENNReal.toReal_div])
  intro N hN
  obtain ⟨k,hk⟩ := small_four N hN
  refine ⟨cylinder (k+5) 4,(open_cylinder _ _).measurableSet,hk,?_,tube_four hcount lam hvol k⟩
  rw [cyl_mass lam hvol]
  simp only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  positivity

theorem realized (hcount : admissibleCount) :
    ∃ lam : Measure K, lam.IsAddHaarMeasure ∧ lam integers = 1 ∧
      ∃ m : RamTransport.H K → Measure (RamTransport.W K), RamTransport.family K lam m ∧
        m (hermScal K TargetOne.conjG 4) (RamTransport.lattice K integers) = (257/128 : ℝ≥0∞) := by
  obtain ⟨lam,hl,hvol⟩ := standard_exists
  obtain ⟨m,hm⟩ := RamTransport.family_exists K locally lam hl
  exact ⟨lam,hl,hvol,m,hm,original_mass hcount lam hl hvol m hm⟩

end RamTransportFour
#print axioms RamTransportFour.original_mass
#print axioms RamTransportFour.realized
