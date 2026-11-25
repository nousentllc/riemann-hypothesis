import FourCounts
import Tubes
open TargetOne MeasureTheory
open scoped ENNReal
noncomputable section
namespace TargetFour
def evenBox : Set (Idx → K) := Set.univ.pi fun _ => cylinder 1 0

theorem digit_parity {r : ℕ} (hr : 1≤r) {b : ZMod (2^r)} {x : K} (hx : x ∈ cylinder r b) :
    x ∈ cylinder 1 0 ↔ b.val % 2=0 := by
  obtain ⟨y,hy,rfl⟩ := hx
  have inj : Function.Injective inc := fun _ _ h => ei.injective (Subtype.coe_injective h)
  have H : inc y ∈ cylinder 1 0 ↔ digit 1 y = 0 := by
    constructor
    · rintro ⟨z,hz,he⟩; exact inj he ▸ hz
    · intro h; exact ⟨y,h,rfl⟩
  rw [H]
  have hc : (ZMod.cast b : ZMod (2^1))=digit 1 y := by
    rw [← show digit r y = b from hy]
    exact PadicInt.cast_toZModPow 1 r hr y
  rw [← hc,ZMod.cast_eq_val]
  exact (ZMod.natCast_eq_natCast_iff b.val 0 2)

abbrev evenGood (r : ℕ) := {v : Idx → ZMod (2^r) // Q v=4 ∧ ∀ i,(v i).val % 2=0}
theorem even_boxes (r : ℕ) (hr : 1≤r) :
    tube r 4 ∩ evenBox = ⋃ v : evenGood r, box v.1 := by
  ext x
  constructor
  · rintro ⟨h,hx⟩
    rw [boxes] at h
    obtain ⟨v,hv⟩ := Set.mem_iUnion.mp h
    refine Set.mem_iUnion.mpr ⟨⟨v.1,v.2,fun i => ?_⟩,hv⟩
    exact (digit_parity hr (hv i (Set.mem_univ _))).mp (hx i (Set.mem_univ _))
  · intro h
    obtain ⟨v,hv⟩ := Set.mem_iUnion.mp h
    refine ⟨?_,fun i _ => (digit_parity hr (hv i (Set.mem_univ _))).mpr (v.2.2 i)⟩
    rw [boxes]
    exact Set.mem_iUnion.mpr ⟨⟨v.1,v.2.1⟩,hv⟩

theorem pair_count (r : ℕ) : Nat.card (evenGood r)=evenCount (2^r) := by
  let e : Idx ≃ Fin 6 := finProdFinEquiv
  apply Nat.card_congr (Equiv.subtypeEquiv (Equiv.arrowCongr e (Equiv.refl (ZMod (2^r)))) ?_)
  intro x
  have h := e.symm.sum_comp (fun i => x i^2)
  change ((∑ i, x i^2)=4 ∧ ∀ i, (x i).val%2=0) ↔
    ((∑ j, x (e.symm j)^2)=4 ∧ ∀ j,(x (e.symm j)).val%2=0)
  rw [h]
  exact and_congr_right fun _ => e.symm.surjective.forall

theorem even_tube_mass (lam : Measure K) [lam.IsAddHaarMeasure] [SigmaFinite lam]
    (hlam : lam (O : Set K)=1) (r : ℕ) (hr : 1≤r) :
    (Measure.pi fun _ : Idx => lam) (tube r 4 ∩ evenBox) =
       (evenCount (2^r) : ℝ≥0∞)*(1/(2^r : ℝ≥0∞))^6 := by
  classical
  have dis : Pairwise (fun v w : evenGood r => Disjoint (box v.1) (box w.1)) := by
    intro v w h
    apply Set.disjoint_left.mpr
    intro x hx hx'
    apply h; apply Subtype.ext; funext i
    by_contra hn
    exact Set.disjoint_left.mp (disjoint_cyl r hn) (hx i (Set.mem_univ _)) (hx' i (Set.mem_univ _))
  have hm (v : evenGood r) : MeasurableSet (box v.1) :=
    MeasurableSet.pi Set.countable_univ fun i _ => (open_cylinder r _).measurableSet
  rw [even_boxes r hr,measure_iUnion dis hm,tsum_fintype]
  have hb (v : evenGood r) : (Measure.pi fun _ : Idx => lam) (box v.1) = (1/(2^r : ℝ≥0∞))^6 := by
    rw [box,Measure.pi_pi]
    simp only [cyl_mass lam hlam,Finset.prod_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
  rw [Finset.sum_congr rfl fun v _ => hb v,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  congr 2
  rw [← Nat.card_eq_fintype_card]
  exact_mod_cast pair_count r

private theorem ratio (N a r : ℕ) (hn : 64*N=a*(2^r)^5) :
    (N:ℝ≥0∞)*(1/(2^r:ℝ≥0∞))^6=(a/64:ℝ≥0∞)*(1/(2^r:ℝ≥0∞)) := by
  have h : (64:ℝ)*N=a*(2^r:ℝ)^5 := by exact_mod_cast hn
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_natCast,
    ENNReal.toReal_one,ENNReal.toReal_ofNat]
  field_simp
  nlinarith

theorem total_tube (lam : Measure K) [lam.IsAddHaarMeasure] [SigmaFinite lam]
    (hlam : lam (O : Set K)=1) (r : ℕ) (hr : 4≤r) :
    (Measure.pi fun _ : Idx => lam) (tube r 4)=(63/64:ℝ≥0∞)*lam (cylinder r 4) := by
  rw [tube_mass lam hlam,cyl_mass lam hlam]
  exact ratio _ 63 _ (by simpa [if_neg (by omega : ¬r<4)] using total_all r)

theorem even_tube (lam : Measure K) [lam.IsAddHaarMeasure] [SigmaFinite lam]
    (hlam : lam (O : Set K)=1) (r : ℕ) (hr : 4≤r) :
    (Measure.pi fun _ : Idx => lam) (tube r 4 ∩ evenBox)=(3/64:ℝ≥0∞)*lam (cylinder r 4) := by
  rw [even_tube_mass lam hlam r (by omega),cyl_mass lam hlam]
  apply ratio
  simpa [show r≠0 by omega,show r≠1 by omega,show ¬r<4 by omega] using even_all r
end TargetFour
#print axioms TargetFour.even_tube
