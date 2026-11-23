import SevenDescent
import SlotGap

open NumberField Formalism.GaloisCohomology Formalism.HC UpperTheory.Top UpperTheory.V
  UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win UpperTheory.V.Base

namespace Seven.Caps

/-- Empty center index, rank zero, and the order-one root suffice at any prime when
every positive-weight layer invariant actually vanishes. The index jZero p 0 is legal. -/
theorem zeroFromLayers (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F]
    (hz : ∀ j : ℕ, 1 ≤ j → ∀ (m : ℕ) (E : Type) [Field E] [NumberField E]
      [Algebra F E], IsLayer p m F E → shaInv E p (j:ℤ) = 0) : ABound p 0 F := by
  constructor
  · refine ⟨ℚ_[p],inferInstance,inferInstance,inferInstance,0,0,Fin.elim0,le_rfl,?_,?_⟩
    · exact ⟨1,by simp⟩
    · intro j hj m E _ _ _ hE B _
      rw [hz j hj m E hE]
      exact zero_le
  · intro j hj m E _ _ _ hE E₂ _ _ _ _ Ω _ _ _ D
    rw [hz j hj m E hE]
    exact zero_le

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem threeZero : ABound 3 0 SlotThree.L :=
  zeroFromLayers 3 SlotThree.L (fun j hj m E _ _ _ hE => SlotThree.Complete.layer_invariant_zero j hj m E hE)

theorem sevenZero (h : Seven.Descent.TowerFree 7 Seven.Descent.L) : ABound 7 0 Seven.Descent.L :=
  zeroFromLayers 7 Seven.Descent.L (fun j hj m E _ _ _ hE =>
    Seven.Descent.layerZero 7 Seven.Descent.L h Seven.Descent.muSeven m E hE (j:ℤ) (by omega))

end Seven.Caps
#print axioms Seven.Caps.zeroFromLayers
#print axioms Seven.Caps.threeZero
#print axioms Seven.Caps.sevenZero
