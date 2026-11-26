import PivotOverlap

open MeasureTheory Topology Set
open scoped ENNReal NNReal
noncomputable section
namespace PivotOverlap
open RamField FourChart

theorem five_norm : ‖(5:K)‖=1 := by
  have h : ‖(4:K)‖<1 := by rw [show (4:K)=2^2 by norm_num,norm_scale]; norm_num
  rw [show (5:K)=1+4 by norm_num,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h.ne'),
    norm_one,max_eq_left h.le]

theorem affine_cell (m : ℕ) (a : K) :
    cell m (a/5) = (fun u : D => (a+2^m*u.val)/5) '' univ := by
  ext x
  constructor
  · intro hx
    refine ⟨⟨(5*x-a)/2^m,(mem_D _).mpr ?_⟩,mem_univ _,?_⟩
    · rw [norm_div,norm_scale,div_le_one₀ (by positivity),
        show 5*x-a=5*(x-a/5) by ring,norm_mul,five_norm,one_mul]
      exact hx
    · change (a+2^m*((5*x-a)/2^m))/5=x
      field_simp; ring
  · rintro ⟨u,_,rfl⟩
    change ‖(a+2^m*u.val)/5-a/5‖ ≤ _
    rw [show (a+2^m*u.val)/5-a/5=2^m*u.val/5 by ring,norm_div,five_norm,div_one,norm_mul,norm_scale]
    simpa using mul_le_mul_of_nonneg_left ((mem_D _).mp u.2) (by positivity : 0 ≤ (1/2:ℝ)^m)

theorem patch_inside (u v : D) (z : Z) :
    (point u v z).1 ∈ cell 3 2 ∧ (point u v z).2 ∈ transverse 3 0 := by
  have ub (a : D) := (mem_D _).mp a.2
  constructor
  · change ‖(-6+128*u.val)/5-2‖ ≤ _
    rw [show (-6+128*u.val)/5-2= 2^4*(-1+8*u.val)/5 by ring,norm_div,five_norm,div_one,norm_mul,norm_scale]
    have h := ub (-1+8*u)
    change ‖-1+8*u.val‖ ≤ 1 at h
    norm_num at *; linarith
  · intro j _
    fin_cases j
    · change ‖(8+32*v.val)/5-0‖ ≤ _
      rw [sub_zero,show (8+32*v.val)/5=(2^3)*(1+4*v.val)/5 by ring,norm_div,five_norm,div_one,norm_mul,norm_scale]
      have h := ub (1+4*v)
      change ‖1+4*v.val‖ ≤ 1 at h
      norm_num at *; linarith
    all_goals
      change ‖32*_/5-(0:K)‖ ≤ _
      rw [sub_zero,norm_div,five_norm,div_one,norm_mul,show (32:K)=2^5 by norm_num,norm_scale]
      apply le_trans (mul_le_mul_of_nonneg_left (ub _) (by positivity))
      norm_num

theorem fold_iff (a b : K) : a+a^2=b+b^2 ↔ a=b ∨ a= -1-b := by
  have h : (a+a^2)-(b+b^2)=(a-b)*(1+a+b) := by ring
  constructor
  · intro he
    have hz : (a-b)*(1+a+b)=0 := by rw [←h,he,sub_self]
    rcases mul_eq_zero.mp hz with ha|ha
    · exact Or.inl (sub_eq_zero.mp ha)
    · right; linear_combination ha
  · rintro (rfl|rfl) <;> ring

theorem fold_points :
    (8/5:K) ≠ -8/5 ∧ (-8/5:K)=(8+16*(-1))/5 ∧
    (-6/5:K)^2+(8/5)^2=4 ∧ (-6/5:K)^2+(-8/5)^2=4 := by norm_num

theorem next_digit {R : Type*} [CommRing R] (v h q : R) :
    (v+2*q*h)+(v+2*q*h)^2-(v+v^2)-2*q*h=4*q*(v*h+q*h^2) := by ring

end PivotOverlap
#print axioms PivotOverlap.affine_cell
#print axioms PivotOverlap.patch_inside
#print axioms PivotOverlap.fold_iff
#print axioms PivotOverlap.fold_points
#print axioms PivotOverlap.next_digit
