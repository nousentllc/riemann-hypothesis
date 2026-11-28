import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AutomorphicArithmetic.CharacterBoxes.DivinNOfHypV
import Development.AutomorphicArithmetic.PrimitiveCosets.LevelGmLeOnFamilyScales

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX UpperTheory.Comparison₂ UpperTheory.Top

namespace UrielJoint

/-- A row retained at any point of a fixed late scale transfers to the host
returned by the source core theorem, with its original row parameter Y. -/
theorem sameIndex {ε : ℝ} (F : FamP ε) (eD eL K cHH eK CL x Y : ℝ)
    (late : F.x1 < x) (j : F.Ix x) (window : PairWin (F.L x j).sc Y)
    (row : PairRow Y ε (F.D x j).host)
    (cohom : ∀ i : F.Ix x, VVle (F.D x i).host.E (F.D x i).R.t (Real.sqrt (F.L x i).sc.b))
    (chain : ChainTied F eD eL K cHH eK CL x) :
    ∃ i : F.Ix x,
      (F.D x i).host.q = (F.D x j).host.q ∧
      (F.D x i).host.d = (F.D x j).host.d ∧
      PairWin (F.L x i).sc Y ∧ PairRow Y ε (F.D x i).host ∧
      VVle (F.D x i).host.E (F.D x i).R.t (Real.sqrt (F.L x i).sc.b) ∧
      CoreAtH (F.D x i).host.toHostRaw (F.D x i).host.TT eD eL K cHH eK ε x := by
  obtain ⟨i, core⟩ := tiedCore_of_chainTied F eD eL K cHH eK CL x chain
  refine ⟨i, F.q_eq x i j, F.d_eq x i j, ?_, ?_, cohom i, core⟩
  · unfold PairWin at window ⊢
    simpa only [F.L_x x i late, F.L_x x j late, F.L_J] using window
  · apply (pairRow_iff_rowq Y ε _).2
    rw [F.QS_eq x i j, F.q_eq x i j, F.d_eq x i j]
    exact (pairRow_iff_rowq Y ε _).1 row

/-- The family cohomology interface supplies the pointwise input above on a tail. -/
theorem sameIndexInput {ε : ℝ} (F : FamP ε) (hV : HypV F.toFamCore) :
    ∃ xV : ℝ, ∀ x ≥ xV, ∀ i : F.Ix x,
      VVle (F.D x i).host.E (F.D x i).R.t (Real.sqrt (F.L x i).sc.b) := hV

end UrielJoint
