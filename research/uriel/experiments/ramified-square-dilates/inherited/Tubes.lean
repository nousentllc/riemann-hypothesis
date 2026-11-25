import Cylinders
open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal
noncomputable section
namespace TargetOne
abbrev Idx := Fin 3 × Fin 2
def Q {R : Type*} [CommRing R] (x : Idx → R) := ∑ i, x i ^ 2
def tube (r : ℕ) (b : ZMod (2^r)) : Set (Idx → K) :=
  {x | (∀ i, x i ∈ O) ∧ Q x ∈ cylinder r b}
private def reorder {R : Type*} [CommRing R] (b : R) :
    {x : Idx → R // Q x=b} ≃ {y : Fin 6 → R // sqSum y=b} :=
  let e : Idx ≃ Fin 6 := finProdFinEquiv
  Equiv.subtypeEquiv (Equiv.arrowCongr e (Equiv.refl R)) fun x => by
    have h := e.symm.sum_comp (fun i => x i ^ 2)
    change (∑ i, x i^2) = b ↔ (∑ j, x (e.symm j)^2) = b
    rw [h]
abbrev good (r : ℕ) (b : ZMod (2^r)) := {v : Idx → ZMod (2^r) // Q v=b}
def box {r : ℕ} (v : Idx → ZMod (2^r)) : Set (Idx → K) := Set.univ.pi (fun i => cylinder r (v i))
theorem boxes (r : ℕ) (b : ZMod (2^r)) : tube r b = ⋃ v : good r b, box v.1 := by
  classical
  have hinj : Function.Injective inc := fun _ _ h => ei.injective (Subtype.coe_injective h)
  ext x
  constructor
  · rintro ⟨hi,z,hz,hq⟩
    choose y hy using fun i => ei.surjective (⟨x i,hi i⟩ : O)
    have he (i) : inc (y i)= x i := congrArg Subtype.val (hy i)
    have hq' : inc (Q y) = Q x := by simp only [Q,map_sum,map_pow,he]
    have hs := hinj (hq'.trans hq.symm)
    let v : good r b := ⟨fun i => digit r (y i), by
      change (∑ i, (digit r (y i))^2) = b
      calc
        _ = digit r (Q y) := by simp only [Q,map_sum,map_pow]
        _ = b := hs ▸ hz⟩
    exact Set.mem_iUnion.mpr ⟨v,fun i _ => ⟨y i,rfl,he i⟩⟩
  · intro h
    obtain ⟨v,hv⟩ := Set.mem_iUnion.mp h
    choose y hy he using fun i => hv i (Set.mem_univ _)
    refine ⟨fun i => he i ▸ (ei (y i)).2, Q y,?_,?_⟩
    · change digit r (Q y) = b
      simpa only [Q,map_sum,map_pow,show ∀ i, digit r (y i)=v.1 i from hy] using v.2
    · simp only [Q,map_sum,map_pow,he]
theorem tube_mass (lam : Measure K) [lam.IsAddHaarMeasure] [SigmaFinite lam]
    (hvol : lam (O : Set K)=1) (r : ℕ) (b : ZMod (2^r)) :
    (Measure.pi fun _ : Idx => lam) (tube r b) =
        (count 6 b : ℝ≥0∞)*(1/(2^r : ℝ≥0∞))^6 := by
  classical
  have dis : Pairwise (fun v w : good r b => Disjoint (box v.1) (box w.1)) := by
    intro v w h
    apply Set.disjoint_left.mpr
    intro x hx hx'
    apply h; apply Subtype.ext; funext i
    by_contra hn
    exact Set.disjoint_left.mp (disjoint_cyl r hn) (hx i (Set.mem_univ _)) (hx' i (Set.mem_univ _))
  have hm (v : good r b) : MeasurableSet (box v.1) :=
    MeasurableSet.pi Set.countable_univ fun i _ => (open_cylinder r _).measurableSet
  rw [boxes,measure_iUnion dis hm,tsum_fintype]
  have hb (v : good r b) : (Measure.pi fun _ : Idx => lam) (box v.1) = (1/(2^r : ℝ≥0∞))^6 := by
    rw [box,Measure.pi_pi]
    simp only [cyl_mass lam hvol, Finset.prod_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
  rw [Finset.sum_congr rfl fun v _ => hb v,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  congr 2
  rw [← Nat.card_eq_fintype_card]
  exact_mod_cast (Nat.card_congr (reorder b))
theorem tube_three_quarters (lam : Measure K) [lam.IsAddHaarMeasure] [SigmaFinite lam]
    (hvol : lam (O : Set K)=1) (k : ℕ) :
    (Measure.pi fun _ : Idx => lam) (tube (k+3) 1) =
      (3/4 : ℝ≥0∞) * lam (cylinder (k+3) 1) := by
  rw [tube_mass lam hvol,cyl_mass lam hvol]
  have h : (4 : ℝ) * count 6 (1 : ZMod (2^(k+3))) = 3*(2^(k+3) : ℝ)^5 := by
    exact_mod_cast count_one_at_depth k
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,
    ENNReal.toReal_natCast,ENNReal.toReal_one,ENNReal.toReal_ofNat]
  field_simp
  nlinarith
end TargetOne
#print axioms TargetOne.tube_three_quarters
