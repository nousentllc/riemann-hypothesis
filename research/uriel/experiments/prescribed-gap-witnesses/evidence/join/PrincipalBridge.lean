import SlotGap
import PhysicalGap
import PairSharing
import FixedRoster

open NumberField Formalism.GaloisCohomology Formalism.HC UpperTheory.Top UpperTheory.V
  UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win EndpointWeights CoherentFields
  UpperTheory.V.Base UpperTheory.V.HV SynchronizedSlots

namespace GapFirst.Bridge


/-- The numerical guard on the genuine source choice follows from the lower
bound on its geometric constant. This holds for every character. -/
theorem four_le_Jchi {K : BConst} (hK : 1 ≤ K.CK) {eps : ℝ}
    (he : 0 < eps) (h52 : eps < 1/52) (psi : PChar) :
    4 ≤ Jchi K 401 eps psi := by
  unfold Jchi BConst.J
  have hbase : (1:ℝ) ≤ 2*K.CK*401/eps := (le_div_iff₀ he).2 (by linarith)
  set R := K.R (AbF.ofChar psi) (Bchi psi) (Lchi psi)
  have hpow : (1:ℝ) ≤ (2*K.CK*401/eps)^R := one_le_pow₀ hbase
  have htwo : (4:ℝ) ≤ 2^(R+2) := by
    rw [pow_add]
    nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := R)]
  exact htwo.trans (le_mul_of_one_le_right (by positivity) hpow)

noncomputable abbrev cut (x : ℝ) := ⌊x^(401:ℝ)⌋₊
noncomputable abbrev Jp (K : BConst) (eps : ℝ) := Jchi K 401 eps PChar.one

/-- Which checks remain at one endpoint of a fixed principal-character gap. -/
def Checks (K : BConst) (wA wB eps : ℝ) (EA : ℕ → Finset ℕ)
    (EB : ℕ → ℕ → Finset ℕ) (outer x : ℝ) : Prop :=
  ActiveSmall (wA*eps/K.CK) (EA (cut outer)) (cut x) x ∧
  ∀ l ∈ Bchi PChar.one, l ≠ 3 → ActiveSmall (wB*eps/K.CK) (EB l (cut outer)) (cut x) x


/-- With the quadratic class-number identity, the entire remaining odd endpoint
work is precisely the slot at 7. Unconditional membership already follows upstream. -/
theorem checksAtSeven (K : BConst) (wA wB eps : ℝ) (EA : ℕ → Finset ℕ)
    (EB : ℕ → ℕ → Finset ℕ) (outer x : ℝ) (h : hStar PChar.one = 1) :
    Checks K wA wB eps EA EB outer x ↔
      ActiveSmall (wA*eps/K.CK) (EA (cut outer)) (cut x) x ∧
      ActiveSmall (wB*eps/K.CK) (EB 7 (cut outer)) (cut x) x := by
  constructor
  · intro hh
    exact ⟨hh.1, hh.2 7 FixedRoster.seven_mem (by decide)⟩
  · rintro ⟨ha,hb⟩
    refine ⟨ha,?_⟩
    intro l hl hne
    rw [FixedRoster.roster_of_class_one h] at hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with hf | hf
    · exact (hne hf).elim
    · simpa [hf] using hb

/-- The target and the queried neighborhood precede all uses of the primes.
The two remaining endpoint tests buy every local WinDatum on the prescribed gap. -/
theorem twoSelections (wA wB : ℝ) (K : BConst) (eps : ℝ)
    (he : 0 < eps) (h52 : eps < 1/52)
    (hwA : 0 ≤ wA*eps/K.CK) (hwB : 0 ≤ wB*eps/K.CK)
    (hj : Across K wA wB 401) (hp : PointHV) (hc : ThmBc 401)
    (e : ℝ → ℕ) (hpage : ∀ x ≥ (1:ℝ), PageN eps x (e x))
    (pex : PairEx) (hK : 1 ≤ K.CK) :
    ∃ T : ℝ, ∃ EB : ℕ → ℕ → Finset ℕ, (∀ l ∈ Bchi PChar.one, OnOldRange (EB l)) ∧
    ∀ a b Y : ℝ, T ≤ Y → Y < a → a ≤ b → b ≤ Y^(Jp K eps) →
    ∃ r > (0:ℝ), ∃ q d : ℕ, ∃ EA : ℕ → Finset ℕ, OnOldRange EA ∧
    ∀ V : ℝ, Y ≤ V → V < Y+r →
    PairGood PChar.one.N eps V (V^(Jp K eps)) q d ∧
    (b^(wA*eps/K.CK) < (cut a : ℝ) → b^(wB*eps/K.CK) < (cut a : ℝ) →
    Checks K wA wB eps EA EB (Y^(Jp K eps)) a →
    Checks K wA wB eps EA EB (V^(Jp K eps)) b →
    ∀ x, a ≤ x → x ≤ b → WinDatum PChar.one eps (Jp K eps) 1 x V q d (e x)) := by
  have hJ : 1 ≤ Jp K eps := (by norm_num : (1:ℝ) ≤ 4).trans (four_le_Jchi hK he h52 _)
  obtain ⟨T,EB,coB,_,byPair⟩ := gapWinDatum wA wB K eps PChar.one he h52 hwA hwB hj hp hc e hpage {3}
    (fun x _ => GapFirst.Slot.principalDirect K eps _ x)
  obtain ⟨P,byY⟩ := SuccessivePairs.prescribedAmbient pex PChar.one.N (by decide) eps (Jp K eps) he h52 hJ
  refine ⟨max P (max T 2),EB,coB,?_⟩
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
  intro ca cb left right x hax hxb
  have hjp : 0 < Jp K eps := by linarith
  have hVpos : 1 ≤ V := by linarith
  have hVX : V ≤ V^(Jp K eps) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hVpos hJ
  have undo : (V^(Jp K eps))^(1/(Jp K eps)) = V := by
    rw [one_div,Real.rpow_rpow_inv (by linarith : 0 ≤ V) hjp.ne']
  have ha' := (ambient (show a ∈ Set.Icc a b from ⟨le_rfl,hab⟩)).1
  have hb' := (ambient (show b ∈ Set.Icc a b from ⟨hab,le_rfl⟩)).2
  have ans := atX (Y^(Jp K eps)) (V^(Jp K eps)) a b
    (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_le_rpow (by linarith) hyv hjp.le) (hT.trans (hyv.trans hVX)) hab
    (hab.trans hb) (by simpa only [← show Jp K eps = Jchi K 401 eps PChar.one from rfl, undo] using ha')
    hb' (by simpa only [← show Jp K eps = Jchi K 401 eps PChar.one from rfl, undo] using pg)
    ca cb left.1 right.1
    (fun l hl hn => left.2 l hl (by simpa using hn))
    (fun l hl hn => right.2 l hl (by simpa using hn)) x hax hxb
  simpa only [← show Jp K eps = Jchi K 401 eps PChar.one from rfl, undo] using ans

end GapFirst.Bridge
#print axioms GapFirst.Bridge.four_le_Jchi
#print axioms GapFirst.Bridge.checksAtSeven
#print axioms GapFirst.Bridge.twoSelections
