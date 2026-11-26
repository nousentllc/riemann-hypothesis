import TargetFourHaar
import RamFieldIntegers
import RamBasePivot
import Mathlib.Topology.MetricSpace.Contracting

open MeasureTheory Topology Set
open scoped ENNReal NNReal
noncomputable section
namespace FourChart
open RamField

abbrev D := inc.range

theorem norm_two : ‖(2:K)‖ = 1/2 := by
  rw [←map_ofNat (algebraMap ℚ_[2] K) 2, norm_algebraMap']
  simpa using Padic.norm_p (p:=2)

theorem mem_D (x : K) : x ∈ integers ↔ ‖x‖ ≤ 1 := by
  rw [integers_eq_unit_ball,Metric.mem_closedBall,dist_zero_right]

theorem sum_bound (x y : D) : ‖x.val+y.val‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((mem_D _).mp x.2) ((mem_D _).mp y.2))

def pivot (x : D) : D := x+2*x^2

theorem pivot_isometry : Isometry pivot := by
  apply Isometry.of_dist_eq
  intro x y
  change dist (x.val+2*x.val^2) (y.val+2*y.val^2) = dist x.val y.val
  simp only [dist_eq_norm]
  rw [show x.val+2*x.val^2-(y.val+2*y.val^2)=(x.val-y.val)*(1+2*(x.val+y.val)) by ring,norm_mul]
  have hlt : ‖(2:K)*(x.val+y.val)‖ < 1 := by rw [norm_mul,norm_two]; linarith [sum_bound x y]
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact ne_of_gt hlt),norm_one,max_eq_left hlt.le,mul_one]

def iteration (b x : D) : D := b-2*x^2

theorem iteration_contracts (b : D) : ContractingWith (1/2:ℝ≥0) (iteration b) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  change dist (b.val-2*x.val^2) (b.val-2*y.val^2) ≤ ((1/2:ℝ≥0):ℝ)*dist x.val y.val
  rw [dist_eq_norm,dist_eq_norm,show b.val-2*x.val^2-(b.val-2*y.val^2)= -(2*(x.val+y.val))*(x.val-y.val) by ring,norm_mul,norm_neg,norm_mul,norm_two]
  push_cast
  exact mul_le_mul_of_nonneg_right (by linarith [sum_bound x y]) (norm_nonneg _)

theorem pivot_surjective : Function.Surjective pivot := by
  let : CompleteSpace D := integers_compact.isComplete.completeSpace_coe
  let : Nonempty D := ⟨⟨0,(mem_D _).mpr (by simp)⟩⟩
  intro b
  let c := iteration_contracts b
  let u := ContractingWith.fixedPoint (iteration b) c
  have hu := congrArg Subtype.val (c.fixedPoint_isFixedPt (f:=iteration b))
  change b.val-2*u.val^2=u.val at hu
  exact ⟨u,Subtype.ext (by change u.val+2*u.val^2=b.val; linear_combination -hu)⟩

def pivotEquiv : D ≃ᵢ D :=
  { Equiv.ofBijective pivot ⟨pivot_isometry.injective,pivot_surjective⟩ with
    isometry_toFun := pivot_isometry }

def cell (m : ℕ) (a : K) : Set K := {x | ‖x-a‖ ≤ (1/2:ℝ)^m}

theorem cell_closed (m : ℕ) (a : K) : IsClosed (cell m a) := isClosed_le (by fun_prop) continuous_const

theorem norm_scale (m : ℕ) : ‖(2:K)^m‖=(1/2:ℝ)^m := by rw [norm_pow,norm_two]

theorem cell_image (m : ℕ) (a : K) : cell m a = (fun u : D => a+2^m*u.val) '' univ := by
  ext x
  constructor
  · intro hx
    refine ⟨⟨(x-a)/2^m,(mem_D _).mpr ?_⟩,mem_univ _,?_⟩
    · rw [norm_div,norm_scale,div_le_one₀ (by positivity)]; exact hx
    · change a+2^m*((x-a)/2^m)=x
      field_simp
      ring
  · rintro ⟨u,_,rfl⟩
    change ‖a+2^m*u.val-a‖ ≤ _
    rw [add_sub_cancel_left,norm_mul,norm_scale]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ((mem_D _).mp u.2) (by positivity : 0 ≤ (1/2:ℝ)^m)

theorem cell_volume (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers = 1)
    (m : ℕ) (a : K) : lam (cell m a) = 1/(2^m:ℝ≥0∞)^2 := by
  have h0 : cell m 0 = RamDilate.StableOdd.precisionCell (2*m) 0 := by
    rw [cell_image]
    ext x
    constructor
    · rintro ⟨⟨_,u,rfl⟩,_,rfl⟩
      refine ⟨2^m*u,?_,?_⟩
      · change (RamDilate.OddCell.pi:O)^(2*m) ∣ 2^m*u-0
        rw [pow_mul,RamDilate.OddCell.pi_sq,sub_zero]; exact dvd_mul_right _ _
      · simp [map_ofNat]
    · rintro ⟨y,hy,rfl⟩
      change (RamDilate.OddCell.pi:O)^(2*m) ∣ y-0 at hy
      rw [pow_mul,RamDilate.OddCell.pi_sq,sub_zero] at hy
      obtain ⟨z,rfl⟩ := hy
      exact ⟨⟨inc z,z,rfl⟩,mem_univ _,by simp [map_ofNat]⟩
  have ht : (fun x : K => -a+x) ⁻¹' cell m 0 = cell m a := by
    ext x; change ‖-a+x-0‖ ≤ _ ↔ ‖x-a‖ ≤ _
    rw [sub_zero,sub_eq_neg_add]
  rw [←ht,measure_preimage_add,h0,RamDilate.StableOdd.even_cell,cyl_mass lam hvol]

abbrev W := Fin 5 → K
abbrev WD := Fin 5 → D

def gram (x : K) (w : W) : K := x^2 + ∑ j, w j ^ 2

def six {R : Type*} (x : R) (w : Fin 5 → R) (j : TargetOne.Idx) : R :=
  (![![x,w 0],![w 1,w 2],![w 3,w 4]] : Fin 3 → Fin 2 → R) j.1 j.2

theorem original_gram (x : K) (w : W) : TargetOne.Q (six x w) = gram x w := by
  simp [TargetOne.Q,gram,six,Fintype.sum_prod_type,Fin.sum_univ_succ]
  ring

def offset (w : WD) : D := 2*∑ j, w j^2

def normalized : D × WD ≃ₜ D × WD where
  toFun p := (pivot p.1 + offset p.2,p.2)
  invFun p := (pivotEquiv.symm (p.1-offset p.2),p.2)
  left_inv := by
    rintro ⟨x,w⟩; simp only [add_sub_cancel_right]; exact Prod.ext (pivotEquiv.symm_apply_apply _) rfl
  right_inv := by
    rintro ⟨t,w⟩
    change (pivotEquiv (pivotEquiv.symm (t-offset w))+offset w,w)=(t,w)
    rw [pivotEquiv.apply_symm_apply,sub_add_cancel]
  continuous_toFun := by
    have hp := pivot_isometry.continuous
    unfold offset
    fun_prop
  continuous_invFun := by
    have hp := pivotEquiv.symm.continuous
    unfold offset
    fun_prop

def physical (p : D × WD) : K × W := (2+8*p.1.val,fun j => 8*(p.2 j).val)
def scalarTarget (t : D) : K := 4+32*t.val

theorem chart_equation (p : D × WD) :
    TargetOne.Q (six (physical p).1 (physical p).2) = scalarTarget (normalized p).1 := by
  rw [original_gram]
  rcases p with ⟨u,w⟩
  change (2+8*u.val)^2 + ∑ j, (8*(w j).val)^2 = 4 + 32*((u+2*u^2+offset w:D):K)
  simp [offset, Fin.sum_univ_succ, show ((2:D):K) = 2 from rfl]; ring

def graph (t : D) (w : WD) := physical (normalized.symm (t,w))

theorem graph_skew (t : D) (w : WD) :
    TargetFourHaar.skewBorel (TargetOne.Q (six (graph t w).1 (graph t w).2)) =
    TargetFourHaar.skewBorel (scalarTarget t) := by
  unfold graph
  rw [chart_equation,normalized.apply_symm_apply]

theorem graph_continuous : Continuous (fun p : D × WD => graph p.1 p.2) := by
  have h : Continuous physical := by unfold physical; fun_prop
  exact h.comp normalized.symm.continuous

theorem delta_norm {x y : K} (hx : x ∈ cell 3 2) (hy : y ∈ cell 3 2) :
    ‖x^2-y^2‖=(1/4:ℝ)*‖x-y‖ := by
  rw [cell_image] at hx hy
  obtain ⟨u,_,rfl⟩ := hx
  obtain ⟨v,_,rfl⟩ := hy
  have h := pivot_isometry.dist_eq u v
  change dist (u.val+2*u.val^2) (v.val+2*v.val^2)=dist u.val v.val at h
  simp only [dist_eq_norm] at h
  rw [show (2+(2:K)^3*u.val)^2-(2+2^3*v.val)^2=2^5*((u.val+2*u.val^2)-(v.val+2*v.val^2)) by ring,
    show (2+(2:K)^3*u.val)-(2+2^3*v.val)=2^3*(u.val-v.val) by ring,
    norm_mul,norm_scale,h,norm_mul,norm_scale]
  ring

/-- The literal readable flat-chart numerator in a hyperbolic plane and one Gaussian
residual coordinate. p+iq is the pivot, a is the free skew coordinate. -/
def hyper (s p q u v a : K) : K × K :=
  let k := (s-u^2-v^2)/(2*(p^2+q^2))
  (p*k-q*a,q*k+p*a)

theorem hyper_equation (s p q u v a : K) (h : p^2+q^2≠0) :
    2*((hyper s p q u v a).1*p+(hyper s p q u v a).2*q)+u^2+v^2=s := by
  unfold hyper; dsimp only; field_simp; ring

theorem hyper_inverse (p q u v x y : K) (h : p^2+q^2≠0) :
    hyper (2*(x*p+y*q)+u^2+v^2) p q u v ((p*y-q*x)/(p^2+q^2)) = (x,y) := by
  apply Prod.ext <;> unfold hyper <;> dsimp only <;> field_simp <;> ring

theorem cell_mono {r m : ℕ} (h : m ≤ r) (a : K) : cell r a ⊆ cell m a :=
  fun _ hx => le_trans hx (pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num) h)

theorem nest {r m : ℕ} {x y a : K} (hm : m ≤ r) (hy : y ∈ cell m a) (hx : x ∈ cell r y) :
    x ∈ cell m a := by
  change ‖x-a‖ ≤ _
  rw [show x-a=(x-y)+(y-a) by ring]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (cell_mono hm y hx) hy)

def transverse (m : ℕ) (a : W) : Set W := univ.pi (fun j => cell m (a j))

theorem transverse_closed (m : ℕ) (a : W) : IsClosed (transverse m a) :=
  isClosed_set_pi (fun j _ => cell_closed m (a j))

theorem transverse_volume (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1)
    (m : ℕ) (a : W) : (Measure.pi fun _ : Fin 5 => lam) (transverse m a) =
      (1/(2^m:ℝ≥0∞)^2)^5 := by
  simp [transverse,Measure.pi_pi,cell_volume lam hvol]

theorem physical_transverse {w : W} (hw : w ∈ transverse 3 0) :
    ∃ z : WD, ∀ j, w j = 8*(z j).val := by
  have hj (j : Fin 5) : ∃ v : D, w j = 8*v.val := by
    have h : w j ∈ cell 3 0 := hw j (mem_univ _)
    rw [cell_image] at h
    obtain ⟨v,_,hv⟩ := h
    exact ⟨v, by simpa only [zero_add,show (2:K)^3=8 by norm_num] using hv.symm⟩
  exact Classical.axiomOfChoice hj

theorem root_formula (t : D) (z : WD) :
    gram (graph t z).1 (fun j => 8*(z j).val) = scalarTarget t := by
  have h := chart_equation (normalized.symm (t,z))
  rw [normalized.apply_symm_apply,original_gram] at h
  exact h

theorem root_box (t : D) (z : WD) : (graph t z).1 ∈ cell 3 2 := by
  rw [cell_image]
  exact ⟨(normalized.symm (t,z)).1,mem_univ _,by norm_num [graph,physical]⟩

theorem root_child (z : WD) : (graph 0 z).1 ∈ cell 4 2 := by
  let u := pivotEquiv.symm (0-offset z)
  have hu := pivotEquiv.isometry.dist_eq u 0
  have he : pivotEquiv u = -offset z := by rw [show pivotEquiv u = _ from pivotEquiv.apply_symm_apply _,zero_sub]
  rw [he,show pivotEquiv 0 = 0 by change (0:D)+2*0^2=0; ring] at hu
  change dist (-(offset z):D).val (0:K) = dist u.val 0 at hu
  rw [dist_zero_right,dist_zero_right] at hu
  have hh : ‖u.val‖ ≤ 1/2 := by
    rw [←hu]
    change ‖-((2:K)*((∑ j, z j^2 : D):K))‖ ≤ _
    rw [norm_neg,norm_mul,norm_two]
    linarith [(mem_D _).mp (∑ j, z j^2 : D).2]
  change ‖2+8*u.val-2‖ ≤ (1/2:ℝ)^4
  rw [add_sub_cancel_left,norm_mul,show (8:K)=2^3 by norm_num,norm_scale]
  norm_num at *; linarith

/-- For a fixed transverse vector each sufficiently fine target tube cuts out one
specific physical pivot cell. Both the center and the scale matter here. -/
theorem slice {m r : ℕ} {w : W} {y a s : K} (hr : m ≤ r)
    (hy : y ∈ cell m a) (hsub : cell m a ⊆ cell 3 2) (hs : gram y w=s) :
    {x : K | x ∈ cell m a ∧ gram x w ∈ cell (r+2) s} = cell r y := by
  ext x
  have hv (hx : x ∈ cell m a) : gram x w ∈ cell (r+2) s ↔ x ∈ cell r y := by
    change ‖gram x w-s‖ ≤ _ ↔ ‖x-y‖ ≤ _
    rw [←hs,gram,gram,add_sub_add_right_eq_sub,delta_norm (hsub hx) (hsub hy),pow_add]
    norm_num
    constructor <;> intro h <;> linarith
  constructor
  · rintro ⟨hx,ht⟩; exact (hv hx).mp ht
  · intro hx
    have hh := nest hr hy hx
    exact ⟨hh,(hv hh).mpr hx⟩

def slab (S : Set W) (m : ℕ) (a : K) (r : ℕ) (s : K) : Set (W × K) :=
  {p | p.1 ∈ S ∧ p.2 ∈ cell m a ∧ gram p.2 p.1 ∈ cell (r+2) s}

theorem slab_meas {S : Set W} (hS : MeasurableSet S) (m : ℕ) (a : K) (r : ℕ) (s : K) :
    MeasurableSet (slab S m a r s) := by
  have h : Continuous (fun p : W × K => gram p.2 p.1) := by unfold gram; fun_prop
  exact (hS.preimage measurable_fst).inter (((cell_closed m a).measurableSet.preimage measurable_snd).inter
    ((cell_closed (r+2) s).measurableSet.preimage h.measurable))

theorem slab_mass (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1)
    (kap : Measure W) {S : Set W} (hS : MeasurableSet S) {m r : ℕ} {a s : K}
    (hr : m ≤ r) (hsub : cell m a ⊆ cell 3 2)
    (hroot : ∀ w ∈ S, ∃ y ∈ cell m a, gram y w=s) :
    (kap.prod lam) (slab S m a r s) = kap S * (1/(2^r:ℝ≥0∞)^2) := by
  rw [Measure.prod_apply (slab_meas hS ..)]
  calc
    _ = ∫⁻ w, S.indicator (fun _ : W => (1/(2^r:ℝ≥0∞)^2)) w ∂kap := by
      apply lintegral_congr
      intro w
      by_cases hw : w ∈ S
      · obtain ⟨y,hy,hs⟩ := hroot w hw
        simpa [slab,Set.preimage,hw,slice hr hy hsub hs] using cell_volume lam hvol r y
      · simp [slab,Set.preimage,hw]
    _ = _ := by rw [lintegral_indicator_const hS,mul_comm]

theorem centered_slabs (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1)
    (kap : Measure W) {S : Set W} (hS : MeasurableSet S) (hbox : S ⊆ transverse 3 0)
    {m r : ℕ} (hm : 3 ≤ m) (hm' : m ≤ 4) (hr : m ≤ r) :
    (kap.prod lam) (slab S m 2 r 4) = kap S * (1/(2^r:ℝ≥0∞)^2) := by
  apply slab_mass lam hvol kap hS hr (cell_mono hm 2)
  intro w hw
  obtain ⟨z,hz⟩ := physical_transverse (hbox hw)
  refine ⟨(graph 0 z).1, cell_mono hm' 2 (root_child z),?_⟩
  rw [show w = _ from funext hz,root_formula]; simp [scalarTarget]

end FourChart
#print axioms FourChart.pivot_surjective
#print axioms FourChart.chart_equation
#print axioms FourChart.graph_skew
#print axioms FourChart.delta_norm
#print axioms FourChart.slab_mass
