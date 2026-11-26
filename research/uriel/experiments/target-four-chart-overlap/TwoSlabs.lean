import OverlapEndpoint

open MeasureTheory Topology Set
open scoped ENNReal NNReal
noncomputable section
namespace PivotOverlap
open RamField FourChart

def yCoords : Fin 5 → Set K := Fin.cons (cell 7 (-6/5)) (fun _ => cell 5 0)
def yBox : Set W := univ.pi yCoords

theorem yMeas : MeasurableSet yBox := by
  apply MeasurableSet.univ_pi
  intro i
  refine Fin.cases ?_ (fun _ => ?_) i <;> exact (cell_closed ..).measurableSet

theorem yVol (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1) :
    transverseHaar lam yBox = (1/4:ℝ≥0∞)^27 := by
  rw [transverseHaar,yBox,Measure.pi_pi]
  simp [yCoords,Fin.prod_univ_succ,cell_volume lam hvol]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_div,ENNReal.toReal_ofNat]

theorem yDelta {x y : K} (hx : x∈cell 5 (8/5)) (hy : y∈cell 5 (8/5)) :
    ‖x^2-y^2‖=(1/2:ℝ)^4*‖x-y‖ := by
  rw [affine_cell] at hx hy
  obtain ⟨u,_,rfl⟩ := hx
  obtain ⟨v,_,rfl⟩ := hy
  have h : ‖2*(u.val+v.val)‖<1 := by rw [norm_mul,norm_two]; linarith [sum_bound u v]
  have hs : ‖1+2*(u.val+v.val)‖=1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h.ne'),
      norm_one,max_eq_left h.le]
  rw [show ((8+(2:K)^5*u.val)/5)^2-((8+2^5*v.val)/5)^2 =
    (2^4*(1+2*(u.val+v.val))/5)*((8+2^5*u.val)/5-(8+2^5*v.val)/5) by ring,
    norm_mul,norm_div,norm_mul,norm_scale,hs,five_norm,mul_one,div_one]

def yTail (u : D) (z : Z) : W :=
  Fin.cons ((-6+128*u.val)/5) (fun j => 32*(z j).val/5)

theorem reordered (u v : D) (z : Z) :
    gram ((8+32*v.val)/5) (yTail u z) = label (A u+B v+C z) := by
  rw [←gram_point,original_gram]
  simp only [gram,yTail,point,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
  ring

theorem yDecode (w : W) (hw : w∈yBox) : ∃ u z, w=yTail u z := by
  have hu : w 0 ∈ cell 7 (-6/5) := hw 0 (mem_univ _)
  rw [affine_cell] at hu
  obtain ⟨u,_,hu⟩ := hu
  have hz (j : Fin 4) : ∃ a : D, 32*a.val/5=w j.succ := by
    have h : w j.succ ∈ cell 5 0 := hw j.succ (mem_univ _)
    rw [show (0:K)=0/5 by ring,affine_cell] at h
    obtain ⟨a,_,h⟩ := h
    exact ⟨a,by norm_num at h ⊢; exact h⟩
  choose z hz using hz
  refine ⟨u,z,funext (fun i => Fin.cases ?_ (fun j => (hz j).symm) i)⟩
  norm_num at hu
  exact hu.symm

theorem yCell (v : D) : (8+32*v.val)/5 ∈ cell 5 (8/5:K) := by
  rw [affine_cell]; exact ⟨v,mem_univ _,by norm_num⟩

theorem yRoot (t : D) (w : W) (hw : w∈yBox) :
    ∃ y ∈ cell 5 (8/5:K), gram y w=label t := by
  obtain ⟨u,z,rfl⟩ := yDecode w hw
  let v := swapY t z u
  have eqv : A u+B v+C z=t := (solve t z u v).mpr (inverseY t z u).symm
  exact ⟨_,yCell v,(reordered u v z).trans (congrArg label eqv)⟩

def ySlab (r : ℕ) (s : K) : Set (W × K) :=
  {p | p.1∈yBox ∧ p.2∈cell 5 (8/5) ∧ gram p.2 p.1∈cell (r+4) s}

theorem ySlabs (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1)
    (t : D) (r : ℕ) (hr : 5 ≤ r) :
    ((transverseHaar lam).prod lam) (ySlab r (label t)) =
      (1/4:ℝ≥0∞)^27 * (1/(2^r:ℝ≥0∞)^2) := by
  have meas : MeasurableSet (ySlab r (label t)) := by
    have h : Continuous (fun p : W × K => gram p.2 p.1) := by unfold gram; fun_prop
    exact (yMeas.preimage measurable_fst).inter (((cell_closed ..).measurableSet.preimage measurable_snd).inter
      ((cell_closed ..).measurableSet.preimage h.measurable))
  rw [Measure.prod_apply meas]
  calc
    _ = ∫⁻ w, yBox.indicator (fun _ : W => (1/(2^r:ℝ≥0∞)^2)) w ∂(transverseHaar lam) := by
      apply lintegral_congr; intro w
      by_cases hw : w∈yBox
      · obtain ⟨y,hy,he⟩ := yRoot t w hw
        have cut : {x : K | x∈cell 5 (8/5) ∧ gram x w∈cell (r+4) (label t)}=cell r y := by
          ext x
          have test (hx : x∈cell 5 (8/5)) : gram x w∈cell (r+4) (label t) ↔ x∈cell r y := by
            change ‖gram x w-label t‖ ≤ _ ↔ ‖x-y‖ ≤ _
            rw [←he,gram,gram,add_sub_add_right_eq_sub,yDelta hx hy,pow_add]
            norm_num
            constructor <;> intro h <;> linarith
          constructor
          · rintro ⟨hx,ht⟩; exact (test hx).mp ht
          · intro hx; exact ⟨nest hr hy hx,(test (nest hr hy hx)).mpr hx⟩
        simpa [ySlab,Set.preimage,hw,cut] using cell_volume lam hvol r y
      · simp [ySlab,Set.preimage,hw]
    _ = _ := by rw [lintegral_indicator_const yMeas,mul_comm,yVol lam hvol]

theorem same_source_volume (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1)
    (t : D) (k : ℕ) :
    ((transverseHaar lam).prod lam) (slab transverseBox 7 (-6/5) (7+k) (label t)) =
      ((transverseHaar lam).prod lam) (ySlab (5+k) (label t)) := by
  rw [physical_slabs lam hvol t _ (by omega),ySlabs lam hvol t _ (by omega)]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_one,
    ENNReal.toReal_ofNat,pow_add]
  field_simp
  ring

theorem disintegrated_slab (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1)
    (t : D) (k : ℕ) :
    let mass := ((transverseHaar lam).prod lam) (ySlab (5+k) (label t))
    let targetCell := cell (9+k) (label t)
    mass = (1/2^46 : ℝ≥0∞)*lam targetCell ∧
      mass = (1/2^47 : ℝ≥0∞)*((2:ℝ≥0∞) • lam) targetCell := by
  dsimp only
  rw [ySlabs lam hvol t _ (by omega),Measure.smul_apply,smul_eq_mul,cell_volume lam hvol]
  constructor <;> apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp <;>
    simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_one,
      ENNReal.toReal_ofNat,pow_add] <;> field_simp <;> ring

end PivotOverlap
#print axioms PivotOverlap.yDelta
#print axioms PivotOverlap.yRoot
#print axioms PivotOverlap.ySlabs
#print axioms PivotOverlap.same_source_volume
#print axioms PivotOverlap.disintegrated_slab
