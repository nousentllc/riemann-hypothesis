import SevenDescent
import PrincipalBridge

open NumberField Formalism.GaloisCohomology Formalism.HC UpperTheory.Top UpperTheory.V
  UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win EndpointWeights CoherentFields
  UpperTheory.V.Base UpperTheory.V.HV SynchronizedSlots GapFirst.Bridge

noncomputable section
namespace Seven.Window

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Direct bounds on the complete finite odd roster, in the existing rank constants. -/
theorem directOdd (h : Descent.TowerFree 7 Descent.L) (roster : Bchi PChar.one = {3,7})
    (K : BConst) (eps : ℝ) (t : ℝ → ℕ) (x : ℝ) :
    BbAt K (Bchi PChar.one) (Lchi PChar.one) eps t x := by
  intro l hl prime F _ _ hF E _ _ _ hE
  rw [roster] at hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with h3 | h7
  · subst l
    exact @GapFirst.Slot.principalDirect K eps t x 3 (by simp) prime F _ _ hF E _ _ _ hE
  · subst l
    rw [FixedRoster.slot_field] at hF
    exact Descent.zeroOnModel h _ _ F hF E hE _ (Real.exp_pos _).le

/-- Permit the same K and the same chosen tables to be used with odd test exponent zero.
A smaller exponent makes the screening input stronger; the independent direct input
at each fixed slot continues to bypass that screen. -/
theorem zeroOddRate (K : BConst) (wA wB : ℝ) (hB : 0 ≤ wB) (hj : Across K wA wB 401) :
    Across K wA 0 401 := by
  intro M B L aux eps A1 he he'
  obtain ⟨X0,panel⟩ := hj M B L aux eps A1 he he'
  refine ⟨max 1 X0,?_⟩
  intro e t adm
  obtain ⟨EB,coB,capB,pairs⟩ := panel e t adm
  refine ⟨EB,coB,capB,?_⟩
  intro q d pp
  obtain ⟨EA,coA,capA,fields⟩ := pairs q d pp
  refine ⟨EA,coA,capA,?_⟩
  intro X hX log x lo hi a b
  have hJ : 0 < K.J 401 eps M B L := BConst.J_pos K (by norm_num) he _ _ _
  have hX1 := (le_max_left (1:ℝ) X0).trans hX
  have hx1 : 1 ≤ x := (Real.one_le_rpow hX1 (by positivity)).trans lo
  apply fields X ((le_max_right (1:ℝ) X0).trans hX) log x lo hi a
  intro l hl
  rcases b l hl with old | dd
  · left
    intro k hk hkt hmem
    have hk1 : (k:ℝ) ≤ 1 := by simpa using old k hk hkt hmem
    exact hk1.trans (Real.one_le_rpow hx1 (div_nonneg (mul_nonneg hB he.le) K.CK_pos.le))
  · exact Or.inr dd

/-- The set of all odd slots is supplied directly. The statement has precisely the
moving-field crossover and its two authenticated endpoint checks. -/
def MovingWindow (K : BConst) (wA eps : ℝ) (e : ℝ → ℕ) : Prop :=
  ∃ T : ℝ, ∀ a b Y : ℝ, T ≤ Y → Y < a → a ≤ b → b ≤ Y^(Jp K eps) →
    ∃ r > (0:ℝ), ∃ q d : ℕ, ∃ EA : ℕ → Finset ℕ, OnOldRange EA ∧
    ∀ V : ℝ, Y ≤ V → V < Y+r →
    PairGood PChar.one.N eps V (V^(Jp K eps)) q d ∧
    (b^(wA*eps/K.CK) < (cut a : ℝ) →
    ActiveSmall (wA*eps/K.CK) (EA (cut (Y^(Jp K eps)))) (cut a) a →
    ActiveSmall (wA*eps/K.CK) (EA (cut (V^(Jp K eps)))) (cut b) b →
    ∀ x, a ≤ x → x ≤ b → WinDatum PChar.one eps (Jp K eps) 1 x V q d (e x))

theorem movingOnly (h : Descent.TowerFree 7 Descent.L) (roster : Bchi PChar.one = {3,7})
    (wA wB : ℝ) (K : BConst) (eps : ℝ) (he : 0 < eps) (h52 : eps < 1/52)
    (hwA : 0 ≤ wA*eps/K.CK) (hwB : 0 ≤ wB)
    (hj : Across K wA wB 401) (hp : PointHV) (hc : ThmBc 401)
    (e : ℝ → ℕ) (page : ∀ x ≥ (1:ℝ), PageN eps x (e x))
    (pex : PairEx) (hK : 1 ≤ K.CK) : MovingWindow K wA eps e := by
  have hJ : 1 ≤ Jp K eps := (by norm_num : (1:ℝ) ≤ 4).trans (four_le_Jchi hK he h52 _)
  obtain ⟨T,EB,_,_,byPair⟩ := gapWinDatum wA 0 K eps PChar.one he h52 hwA (by simp)
    (zeroOddRate K wA wB hwB hj) hp hc e page (Bchi PChar.one)
    (fun x _ => directOdd h roster K eps _ x)
  obtain ⟨P,byY⟩ := SuccessivePairs.prescribedAmbient pex PChar.one.N (by decide) eps (Jp K eps) he h52 hJ
  refine ⟨max P (max T 2),?_⟩
  intro a b Y hY hYa hab hb
  have hP := (le_max_left P (max T 2)).trans hY
  have hT := ((le_max_left T (2:ℝ)).trans (le_max_right P _)).trans hY
  have hY2 := ((le_max_right T (2:ℝ)).trans (le_max_right P _)).trans hY
  obtain ⟨r,hr,q,d,both⟩ := byY a b Y hP hYa hab hb
  have row := (both Y le_rfl (by linarith)).2
  have pp : PrimePair PChar.one.N q d :=
    ⟨row.pair.q_prime,row.pair.q_mod,row.pair.d_prime,row.pair.d_mod,row.coprime.symm⟩
  obtain ⟨EA,coA,_,atX⟩ := byPair q d pp
  refine ⟨r,hr,q,d,EA,coA,?_⟩
  intro V hyv hv
  obtain ⟨ambient,pg⟩ := both V hyv hv
  refine ⟨pg,?_⟩
  intro ca left right x hax hxb
  have hjp : 0 < Jp K eps := by linarith
  have hVpos : 1 ≤ V := by linarith
  have hVX : V ≤ V^(Jp K eps) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hVpos hJ
  have undo : (V^(Jp K eps))^(1/(Jp K eps)) = V := by
    rw [one_div,Real.rpow_rpow_inv (by linarith : 0 ≤ V) hjp.ne']
  have ha' := (ambient (show a ∈ Set.Icc a b from ⟨le_rfl,hab⟩)).1
  have hb' := (ambient (show b ∈ Set.Icc a b from ⟨hab,le_rfl⟩)).2
  have hcut : (2:ℕ) ≤ cut a := by
    apply Nat.le_floor
    calc (2:ℝ) ≤ a := by linarith
         _ = a ^ (1:ℝ) := (Real.rpow_one a).symm
         _ ≤ a ^ (401:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have cb : b^(0*eps/K.CK) < (cut a : ℝ) := by
    simp only [zero_mul,zero_div,Real.rpow_zero]
    exact_mod_cast (by omega : 1 < cut a)
  have ans := atX (Y^(Jp K eps)) (V^(Jp K eps)) a b
    (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_le_rpow (by linarith) hyv hjp.le) (hT.trans (hyv.trans hVX)) hab
    (hab.trans hb) (by simpa only [← show Jp K eps = Jchi K 401 eps PChar.one from rfl, undo] using ha')
    hb' (by simpa only [← show Jp K eps = Jchi K 401 eps PChar.one from rfl, undo] using pg)
    ca cb left right (fun _ hl hn => (hn hl).elim) (fun _ hl hn => (hn hl).elim) x hax hxb
  simpa only [← show Jp K eps = Jchi K 401 eps PChar.one from rfl, undo] using ans

end Seven.Window
#print axioms Seven.Window.directOdd
#print axioms Seven.Window.zeroOddRate
#print axioms Seven.Window.movingOnly
