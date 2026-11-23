import SevenAscent
import SevenRoster
import SevenCaps
import SevenWindow

open NumberField Formalism.GaloisCohomology Formalism.HC UpperTheory.Top UpperTheory.V
  UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win UpperTheory.V.Base UpperTheory.V.HV
  SynchronizedSlots Seven.Descent

namespace Seven.Complete

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem actualTowerFree : TowerFree 7 L :=
  fun n hn => Seven.Ascent.allCyclotomicLayers n (by omega)

theorem actualRankZero : Subsingleton (UpperTheory.V.Tower.XP 7 L) :=
  moduleZero 7 L actualTowerFree

/-- No arithmetic hypothesis apart from identifying the actual base and layer. -/
theorem allSigned (m : ℕ) (F : Type) [Field F] [NumberField F] (hF : IsAbField (AbF.cyc 7) F)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsLayer 7 m F E)
    (j : ℤ) (hj : j ≠ 0) : shaInv E 7 j = 0 :=
  invariantOnModel actualTowerFree m F hF E hE j hj

theorem localKernel (m : ℕ) (F : Type) [Field F] [NumberField F] (hF : IsAbField (AbF.cyc 7) F)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsLayer 7 m F E)
    (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (D : LData E Ω 7)
    (j : ℤ) (hj : j ≠ 0) : Sha D j = ⊥ :=
  kernelOnModel actualTowerFree m F hF E hE Ω D j hj

theorem localSumZero (m t : ℕ) (F : Type) [Field F] [NumberField F] (hF : IsAbField (AbF.cyc 7) F)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsLayer 7 m F E) :
    VVat 7 E t 0 :=
  zeroOnModel actualTowerFree m t F hF E hE 0 le_rfl

theorem rankZeroBound : ABound 7 0 L := Seven.Caps.sevenZero actualTowerFree

theorem allOdd (K : BConst) (eps : ℝ) (t : ℝ → ℕ) (x : ℝ) :
    BbAt K (Bchi PChar.one) (Lchi PChar.one) eps t x :=
  Seven.Window.directOdd actualTowerFree SevenRoster.principalRoster K eps t x

theorem onlyMoving (wA wB : ℝ) (K : BConst) (eps : ℝ) (he : 0 < eps) (h52 : eps < 1/52)
    (hwA : 0 ≤ wA*eps/K.CK) (hwB : 0 ≤ wB)
    (hj : Across K wA wB 401) (hp : PointHV) (hc : ThmBc 401)
    (e : ℝ → ℕ) (page : ∀ x ≥ (1:ℝ), PageN eps x (e x))
    (pex : PairEx) (hK : 1 ≤ K.CK) : Seven.Window.MovingWindow K wA eps e :=
  Seven.Window.movingOnly actualTowerFree SevenRoster.principalRoster wA wB K eps he h52 hwA hwB
    hj hp hc e page pex hK

end Seven.Complete
#print axioms Seven.Complete.actualTowerFree
#print axioms Seven.Complete.actualRankZero
#print axioms Seven.Complete.allSigned
#print axioms Seven.Complete.localKernel
#print axioms Seven.Complete.localSumZero
#print axioms Seven.Complete.rankZeroBound
#print axioms Seven.Complete.allOdd
#print axioms Seven.Complete.onlyMoving
