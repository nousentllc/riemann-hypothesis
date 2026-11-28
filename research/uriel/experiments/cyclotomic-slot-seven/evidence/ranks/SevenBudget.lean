import LeastSupply
import SevenCaps
import SevenAscent
import SevenRoster
import SevenWindow

open NumberField Formalism.GaloisCohomology Formalism.HC UpperTheory.Top UpperTheory.V
  UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win EndpointWeights CoherentFields
  UpperTheory.V.Base UpperTheory.V.HV SynchronizedSlots

namespace Seven.Ranks
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem availableThree : ZeroRank 3 (AbF.cyc 3) :=
  ⟨inferInstance, SlotThree.L, inferInstance, inferInstance,
    SlotThree.FieldModel.fieldModel, Seven.Caps.threeZero⟩

theorem availableSeven : ZeroRank 7 (AbF.cyc 7) :=
  ⟨inferInstance, Seven.Descent.L, inferInstance, inferInstance, Seven.Descent.fieldModel,
    Seven.Caps.sevenZero (fun n hn => Seven.Ascent.allCyclotomicLayers n (by omega))⟩

/-- Under this new design only the moving rank enters the principal search exponent. -/
theorem principalBudget (K : BConst) (h3 : K.Rl 3 (AbF.cyc 3) = 0)
    (h7 : K.Rl 7 (AbF.cyc 7) = 0) (Ct eps : ℝ) :
    K.R (AbF.ofChar PChar.one) (Bchi PChar.one) (Lchi PChar.one) = K.R0 (AbF.ofChar PChar.one) ∧
    Jchi K Ct eps PChar.one =
      2^(K.R0 (AbF.ofChar PChar.one)+2) * (2*K.CK*Ct/eps)^(K.R0 (AbF.ofChar PChar.one)) := by
  have hR : K.R (AbF.ofChar PChar.one) (Bchi PChar.one) (Lchi PChar.one) =
      K.R0 (AbF.ofChar PChar.one) := by
    simp [BConst.R, SevenRoster.principalRoster, FixedRoster.slot_field, h3, h7]
  exact ⟨hR, by simp [Jchi,BConst.J,hR]⟩

/-- A single redesigned supply choice works across every admissible tolerance:
the two odd ranks are zero, and the actual window needs only the moving tests. -/
theorem leastMovingDesign (hK : ∃ CK : ℝ, LemmaK CK) (fixed : FixedIn) (two : TwoIn)
    (hp : PointHV) (hc : ThmBc 401) (pex : PairEx) :
    ∃ K : BConst, 1 ≤ K.CK ∧ K.Rl 3 (AbF.cyc 3) = 0 ∧ K.Rl 7 (AbF.cyc 7) = 0 ∧
    ∀ eps : ℝ, 0 < eps → eps < 1/52 →
      Jchi K 401 eps PChar.one = 2^(K.R0 (AbF.ofChar PChar.one)+2) *
        (2*K.CK*401/eps)^(K.R0 (AbF.ofChar PChar.one)) ∧
      ∀ e : ℝ → ℕ, (∀ x ≥ (1:ℝ), PageN eps x (e x)) → Seven.Window.MovingWindow K (1/2) eps e := by
  obtain ⟨K,hCK,hz,all⟩ := coherentLeast (1/2) (1/2) (by norm_num) (by norm_num) hK fixed two
  have h3 := hz 3 _ availableThree
  have h7 := hz 7 _ availableSeven
  refine ⟨K,hCK,h3,h7,?_⟩
  intro eps he h52
  refine ⟨(principalBudget K h3 h7 401 eps).2, ?_⟩
  intro e page
  have pos := K.CK_pos
  apply Seven.Window.movingOnly (fun n hn => Seven.Ascent.allCyclotomicLayers n (by omega))
    SevenRoster.principalRoster (1/2) (1/2) K eps he h52 (by positivity) (by positivity)
    (all 401 (by norm_num)) hp hc e page pex hCK

end Seven.Ranks
#print axioms Seven.Ranks.availableThree
#print axioms Seven.Ranks.availableSeven
#print axioms Seven.Ranks.principalBudget
#print axioms Seven.Ranks.leastMovingDesign
