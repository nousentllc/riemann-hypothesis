import FourBoxMeasures

open MeasureTheory Topology Set
open scoped ENNReal NNReal
noncomputable section
namespace PivotOverlap
open RamField FourChart

/-- The displacement from the identity is strictly contracting on the integral ball. -/
def errorTerm (a b x : D) : D := 2*(a*x + b*x^2)
def poly (a b x : D) : D := x + errorTerm a b x

theorem err_bound (a b x y : D) :
    ‖(errorTerm a b x).val-(errorTerm a b y).val‖ ≤ (1/2:ℝ)*‖x.val-y.val‖ := by
  have h : ‖a.val+b.val*(x.val+y.val)‖ ≤ 1 :=
    (mem_D _).mp (a+b*(x+y)).2
  change ‖2*(a.val*x.val+b.val*x.val^2)-2*(a.val*y.val+b.val*y.val^2)‖ ≤ _
  rw [show 2*(a.val*x.val+b.val*x.val^2)-2*(a.val*y.val+b.val*y.val^2) =
    2*(a.val+b.val*(x.val+y.val))*(x.val-y.val) by ring,norm_mul,norm_mul,norm_two]
  exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

theorem poly_iso (a b : D) : Isometry (poly a b) := by
  apply Isometry.of_dist_eq
  intro x y
  change dist (x.val+(errorTerm a b x).val) (y.val+(errorTerm a b y).val) = dist x.val y.val
  simp only [dist_eq_norm]
  rw [show x.val+(errorTerm a b x).val-(y.val+(errorTerm a b y).val) =
    (x.val-y.val)+((errorTerm a b x).val-(errorTerm a b y).val) by ring]
  by_cases h : x=y
  · subst y; simp
  have hp : 0 < ‖x.val-y.val‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun e => h (Subtype.ext e)))
  have hl : ‖(errorTerm a b x).val-(errorTerm a b y).val‖ < ‖x.val-y.val‖ := by
    linarith [err_bound a b x y]
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hl.ne',max_eq_left hl.le]

theorem poly_onto (a b : D) : Function.Surjective (poly a b) := by
  let : CompleteSpace D := integers_compact.isComplete.completeSpace_coe
  let : Nonempty D := ⟨0⟩
  intro t
  let f (x : D) := t-errorTerm a b x
  have hc : ContractingWith (1/2:ℝ≥0) f := by
    refine ⟨by norm_num,LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (t.val-(errorTerm a b x).val) (t.val-(errorTerm a b y).val) ≤ _*dist x.val y.val
    rw [dist_sub_left,dist_eq_norm,dist_eq_norm]
    exact err_bound a b x y
  let u := hc.fixedPoint f
  have h := hc.fixedPoint_isFixedPt (f:=f)
  change t-errorTerm a b u=u at h
  refine ⟨u,?_⟩
  unfold poly
  linear_combination -h

def perm (a b : D) : D ≃ᵢ D :=
  { Equiv.ofBijective (poly a b) ⟨(poly_iso a b).injective,poly_onto a b⟩ with
    isometry_toFun := poly_iso a b }

def A : D ≃ᵢ D := perm (-2) 16
def B : D ≃ᵢ D := perm 0 1
abbrev Z := Fin 4 → D
def C (z : Z) : D := 2*∑ j, z j^2

def swapX (t : D) (z : Z) (v : D) := A.symm (t-C z-B v)
def swapY (t : D) (z : Z) (u : D) := B.symm (t-C z-A u)

theorem solve (t : D) (z : Z) (u v : D) :
    A u+B v+C z=t ↔ u=swapX t z v := by
  unfold swapX
  constructor
  · intro h
    apply A.injective
    rw [A.apply_symm_apply]
    linear_combination h
  · rintro rfl
    rw [A.apply_symm_apply]
    abel

theorem inverseX (t : D) (z : Z) (v : D) : swapY t z (swapX t z v)=v := by
  apply B.injective
  simp [swapY,swapX]
theorem inverseY (t : D) (z : Z) (u : D) : swapX t z (swapY t z u)=u := by
  apply A.injective
  simp [swapY,swapX]

def reflection (t : D) : D ≃ᵢ D where
  toFun x := t-x
  invFun x := t-x
  left_inv _ := sub_sub_cancel _ _
  right_inv _ := sub_sub_cancel _ _
  isometry_toFun := Isometry.of_dist_eq fun x y => by rw [dist_sub_left]

def transition (t : D) (z : Z) : D ≃ᵢ D :=
  (B.trans (reflection (t-C z))).trans A.symm

theorem transition_apply (t : D) (z : Z) (v : D) : transition t z v=swapX t z v := rfl

def point (u v : D) (z : Z) : K × W :=
  ((-6+128*u.val)/5,Fin.cons ((8+32*v.val)/5) (fun j => 32*(z j).val/5))

def label (t : D) : K := (100+512*t.val)/25

theorem gram_point (u v : D) (z : Z) :
    TargetOne.Q (six (point u v z).1 (point u v z).2) = label (A u+B v+C z) := by
  rw [original_gram]
  have aa : (A u).val = u.val+2*((-2)*u.val+16*u.val^2) := rfl
  have bb : (B v).val = v.val+2*(0*v.val+1*v.val^2) := rfl
  simp [point,gram,label,C,aa,bb,Fin.sum_univ_succ,
    show ((2:D):K)=2 from rfl]
  ring

theorem center : label 0 = 4 ∧ ((-6/5:K)^2+(8/5:K)^2=4) := by
  constructor <;> norm_num [label]

end PivotOverlap
#print axioms PivotOverlap.poly_onto
#print axioms PivotOverlap.inverseX
#print axioms PivotOverlap.inverseY
#print axioms PivotOverlap.gram_point
#print axioms PivotOverlap.center
