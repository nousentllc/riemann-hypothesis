import RamTransport

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace RamTransport

variable {K A B : Type} [Field K] [CommRing A] [CommRing B]
variable [MeasurableSpace K]

def residueCell (inc : A →+* K) (digit : A →+* B) (b : B) : Set K :=
  inc '' {x | digit x = b}

omit [MeasurableSpace K] in
private theorem disjoint_cell (inc : A →+* K) (hinj : Function.Injective inc) (digit : A →+* B) :
    Pairwise (fun a b => Disjoint (residueCell inc digit a) (residueCell inc digit b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
  exact hab (hx.symm.trans (hinj he ▸ hy))

abbrev repSol (b : B) := {v : TargetOne.Idx → B // TargetOne.Q v=b}
def residueBox (inc : A →+* K) (digit : A →+* B) (v : TargetOne.Idx → B) :
    Set (TargetOne.Idx → K) := Set.univ.pi fun i => residueCell inc digit (v i)

omit [MeasurableSpace K] in
theorem cell_partition (inc : A →+* K) (hinj : Function.Injective inc) (digit : A →+* B)
    (b : B) :
    tube K (Set.range inc) (residueCell inc digit b) =
      ⋃ v : repSol b, residueBox inc digit v.1 := by
  classical
  ext x
  constructor
  · rintro ⟨hi,z,hz,hq⟩
    choose y he using hi
    have hq' : inc (TargetOne.Q y) = TargetOne.Q x := by simp only [TargetOne.Q,map_sum,map_pow,he]
    have hs := hinj (hq'.trans hq.symm)
    let v : repSol b := ⟨fun i => digit (y i), by
      change (∑ i, (digit (y i))^2) = b
      calc
        _ = digit (TargetOne.Q y) := by simp only [TargetOne.Q,map_sum,map_pow]
        _ = b := hs ▸ hz⟩
    exact Set.mem_iUnion.mpr ⟨v,fun i _ => ⟨y i,rfl,he i⟩⟩
  · intro h
    obtain ⟨v,hv⟩ := Set.mem_iUnion.mp h
    choose y hy he using fun i => hv i (Set.mem_univ _)
    refine ⟨fun i => ⟨y i,he i⟩,TargetOne.Q y,?_,?_⟩
    · change digit (TargetOne.Q y) = b
      simpa only [TargetOne.Q,map_sum,map_pow,show ∀ i, digit (y i)=v.1 i from hy] using v.2
    · simp only [TargetOne.Q,map_sum,map_pow,he]

private def indexEquiv (b : B) :
    repSol b ≃ {y : Fin 6 → B // TargetOne.sqSum y=b} :=
  let e : TargetOne.Idx ≃ Fin 6 := finProdFinEquiv
  Equiv.subtypeEquiv (Equiv.arrowCongr e (Equiv.refl B)) fun x => by
    have h := e.symm.sum_comp (fun i => x i ^ 2)
    change (∑ i, x i^2) = b ↔ (∑ j, x (e.symm j)^2) = b
    rw [h]

/-- A source box has six independent scalar factors.  This identity concerns
ambient measure and uses no disintegration or smoothness assumption. -/
theorem fiber_count_to_tube [Finite B] (inc : A →+* K) (hinj : Function.Injective inc)
    (digit : A →+* B) (lam : Measure K) [SigmaFinite lam]
    (hMeas : ∀ b, MeasurableSet (residueCell inc digit b)) (u : ℝ≥0∞)
    (hMass : ∀ b, lam (residueCell inc digit b) = u) (b : B) :
    (Measure.pi fun _ : TargetOne.Idx => lam) (tube K (Set.range inc) (residueCell inc digit b)) =
      (TargetOne.count 6 b : ℝ≥0∞) * u^6 := by
  classical
  let := Fintype.ofFinite B
  have dis : Pairwise (fun v w : repSol b => Disjoint
      (residueBox inc digit v.1) (residueBox inc digit w.1)) := by
    intro v w h
    apply Set.disjoint_left.mpr
    intro x hx hx'
    apply h; apply Subtype.ext; funext i
    by_contra hn
    exact Set.disjoint_left.mp (disjoint_cell inc hinj digit hn)
      (hx i (Set.mem_univ _)) (hx' i (Set.mem_univ _))
  have hm (v : repSol b) : MeasurableSet (residueBox inc digit v.1) :=
    MeasurableSet.pi Set.countable_univ fun i _ => hMeas _
  rw [cell_partition inc hinj digit b,measure_iUnion dis hm,tsum_fintype]
  have hb (v : repSol b) : (Measure.pi fun _ : TargetOne.Idx => lam) (residueBox inc digit v.1) = u^6 := by
    rw [residueBox,Measure.pi_pi]
    simp only [hMass,Finset.prod_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
  rw [Finset.sum_congr rfl fun v _ => hb v,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  congr 2
  rw [← Nat.card_eq_fintype_card]
  exact_mod_cast (Nat.card_congr (indexEquiv b))

theorem scaled_ratio (n q : ℕ) (hq : q ≠ 0) (h : 128*n = 257*q^5) :
    (n:ℝ≥0∞)*(1/(q:ℝ≥0∞))^6 = (257/128:ℝ≥0∞)*(1/(q:ℝ≥0∞)) := by
  have hn : (128:ℝ)*n = 257*(q:ℝ)^5 := by exact_mod_cast h
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_natCast,
    ENNReal.toReal_one,ENNReal.toReal_ofNat]
  have hq' : (q:ℝ) ≠ 0 := by exact_mod_cast hq
  field_simp
  nlinarith

end RamTransport
#print axioms RamTransport.fiber_count_to_tube
