import FoldImage
import OverlapMeasure

open MeasureTheory Topology Set
open scoped ENNReal NNReal
noncomputable section
namespace PivotOverlap
open RamField FourChart RamDilate.OddCell

def foldD (v : D) : D := v+v^2
def wideOffset (u : D) (z : Z) : D := 2*(A u+C z)
def wideValue (u v : D) (z : Z) : D := wideOffset u z+foldD v

theorem wideGram (u v : D) (z : Z) :
    TargetOne.Q (six ((-6+128*u.val)/5) (Fin.cons ((8+16*v.val)/5)
      (fun j => 32*(z j).val/5))) = (100+256*(wideValue u v z).val)/25 := by
  rw [original_gram]
  have aa : (A u).val=u.val+2*((-2)*u.val+16*u.val^2) := rfl
  simp [gram,wideValue,wideOffset,foldD,C,aa,Fin.sum_univ_succ,
    show ((2:D):K)=2 from rfl]
  ring

theorem norm_centers (r : D) : ‖(1:K)+2*r.val‖=1 := by
  have h : ‖(2:K)*r.val‖<1 := by
    rw [norm_mul,norm_two]; linarith [(mem_D _).mp r.2]
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h.ne'),
    norm_one,max_eq_left h.le]

private theorem sub_ultra (x y : K) : ‖x-y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa only [sub_eq_add_neg,norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)

theorem split_cut (r : D) (d : ℕ) :
    {v : D | foldD v ∈ disc d (foldD r)} = disc d r ∪ disc d (-1-r) := by
  ext v
  change ‖(v.val+v.val^2)-(r.val+r.val^2)‖ ≤ (1/2:ℝ)^d ↔
    ‖v.val-r.val‖ ≤ (1/2:ℝ)^d ∨ ‖v.val-(-1-r.val)‖ ≤ (1/2:ℝ)^d
  have hleft : ‖v.val-r.val‖≤1 := (mem_D _).mp (v-r).2
  have hright : ‖v.val-(-1-r.val)‖≤1 := (mem_D _).mp (v-(-1-r)).2
  have hmax : max ‖v.val-r.val‖ ‖v.val-(-1-r.val)‖=1 := by
    apply le_antisymm (max_le hleft hright)
    rw [←norm_centers r,show 1+2*r.val=(v.val-(-1-r.val))-(v.val-r.val) by ring,max_comm]
    exact sub_ultra _ _
  rw [show (v.val+v.val^2)-(r.val+r.val^2)=(v.val-r.val)*(v.val-(-1-r.val)) by ring,norm_mul]
  rcases le_total ‖v.val-r.val‖ ‖v.val-(-1-r.val)‖ with h|h
  · rw [max_eq_right h] at hmax
    rw [hmax,mul_one]
    exact ⟨Or.inl,fun e => e.elim id (fun w => (h.trans hmax.le).trans w)⟩
  · rw [max_eq_left h] at hmax
    rw [hmax,one_mul]
    exact ⟨Or.inr,fun e => e.elim (fun w => (h.trans hmax.le).trans w) id⟩

theorem disjoint_branches (r : D) (d : ℕ) (hd : 1≤d) :
    Disjoint (disc d r) (disc d (-1-r)) := by
  apply Set.disjoint_left.mpr
  intro v ha hb
  change ‖v.val-r.val‖ ≤ (1/2:ℝ)^d at ha
  change ‖v.val-(-1-r.val)‖ ≤ (1/2:ℝ)^d at hb
  have h := sub_ultra (v.val-(-1-r.val)) (v.val-r.val)
  rw [show (v.val-(-1-r.val))-(v.val-r.val)=1+2*r.val by ring,norm_centers] at h
  have lt : (1/2:ℝ)^d<1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  linarith [h.trans (max_le hb ha)]

theorem fold_cut_mass (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1)
    (r : D) (d : ℕ) (hd : 1≤d) :
    integralHaar lam {v : D | foldD v∈disc d (foldD r)}=2*(1/(2^d:ℝ≥0∞)^2) := by
  rw [split_cut,measure_union (disjoint_branches r d hd) Metric.isClosed_closedBall.measurableSet,
    disc_mass lam hvol,disc_mass lam hvol,two_mul]

theorem wide_root (t : O) (u : D) (z : Z) :
    (∃ v : D, wideValue u v z=orderEquiv t) ↔ (pi:O) ∣ t := by
  let b := orderEquiv.symm (A u+C z)
  have hb : orderEquiv b=A u+C z := orderEquiv.apply_symm_apply _
  have h : (∃ v : D, wideValue u v z=orderEquiv t) ↔ ∃ w : O, fold w=t-2*b := by
    constructor
    · rintro ⟨v,hv⟩
      refine ⟨orderEquiv.symm v,orderEquiv.injective ?_⟩
      simp only [fold,map_add,map_pow,map_sub,map_mul,map_ofNat,RingEquiv.apply_symm_apply,hb]
      change 2*(A u+C z)+(v+v^2)=orderEquiv t at hv
      linear_combination hv
    · rintro ⟨w,hw⟩
      refine ⟨orderEquiv w,?_⟩
      have hh := congrArg orderEquiv hw
      simp only [fold,map_add,map_pow,map_sub,map_mul,map_ofNat,hb] at hh
      change 2*(A u+C z)+(orderEquiv w+(orderEquiv w)^2)=orderEquiv t
      linear_combination hh
  rw [h,image_digit,pi_condition]
  simp only [map_sub,map_mul,map_ofNat,show (2:R 1)=0 by decide,zero_mul,sub_zero]

theorem wide_section (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1)
    (t : O) (ht : (pi:O)∣t) (u : D) (z : Z) (d : ℕ) (hd : 1≤d) :
    integralHaar lam {v : D | wideValue u v z ∈ disc d (orderEquiv t)} =
      2*(1/(2^d:ℝ≥0∞)^2) := by
  obtain ⟨r,hr⟩ := (wide_root t u z).mpr ht
  have he : {v : D | wideValue u v z∈disc d (orderEquiv t)} =
      {v : D | foldD v∈disc d (foldD r)} := by
    ext v
    rw [←hr]
    change dist (wideOffset u z+foldD v) (wideOffset u z+foldD r) ≤ _ ↔ dist (foldD v) (foldD r) ≤ _
    rw [dist_add_left]
  rw [he,fold_cut_mass lam hvol r d hd]

theorem wide_tube (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1)
    (nu : Measure P) [IsProbabilityMeasure nu] (t : O) (ht : (pi:O)∣t)
    (d : ℕ) (hd : 1≤d) :
    (nu.prod (integralHaar lam)) {p : P × D |
      wideValue p.1.2 p.2 p.1.1 ∈ disc d (orderEquiv t)} = 2*(1/(2^d:ℝ≥0∞)^2) := by
  let : IsProbabilityMeasure (integralHaar lam) := ⟨integral_univ lam hvol⟩
  have hh : Continuous (fun p : P × D => wideValue p.1.2 p.2 p.1.1) := by
    have ha := A.continuous
    have hc := contC
    unfold wideValue wideOffset foldD
    fun_prop
  have hm : MeasurableSet {p : P × D | wideValue p.1.2 p.2 p.1.1 ∈ disc d (orderEquiv t)} :=
    (Metric.isClosed_closedBall (x:=orderEquiv t) (ε:=(1/2:ℝ)^d)).measurableSet.preimage hh.measurable
  rw [Measure.prod_apply hm]
  calc
    _ = ∫⁻ _ : P, 2*(1/(2^d:ℝ≥0∞)^2) ∂nu := by
      apply lintegral_congr; intro p; exact wide_section lam hvol t ht p.2 p.1 d hd
    _ = _ := by simp

theorem wide_units (d : ℕ) :
    (1/4^31 : ℝ≥0∞)*(2*(1/(2^d:ℝ≥0∞)^2)) =
      (1/2^45 : ℝ≥0∞)*(1/(2^(8+d):ℝ≥0∞)^2) ∧
    (1/4^31 : ℝ≥0∞)*(2*(1/(2^d:ℝ≥0∞)^2)) =
      (1/2^46 : ℝ≥0∞)*(2*(1/(2^(8+d):ℝ≥0∞)^2)) := by
  constructor <;> apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp <;>
    simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_one,
      ENNReal.toReal_ofNat,pow_add] <;> field_simp <;> ring

end PivotOverlap
#print axioms PivotOverlap.wideGram
#print axioms PivotOverlap.fold_cut_mass
#print axioms PivotOverlap.wide_root
#print axioms PivotOverlap.wide_section
#print axioms PivotOverlap.wide_tube
#print axioms PivotOverlap.wide_units
