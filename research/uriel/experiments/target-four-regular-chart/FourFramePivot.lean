import FourChart
import GaussianFrame

open RamField
noncomputable section
namespace FourChart

abbrev GInt := QuadraticAlgebra D (-1) 0
def includeGaussian (z : GInt) : GaussianFrame.G K := ⟨z.re.val,z.im.val⟩
def framePivot (c : D) (a b d : GInt) : GaussianFrame.G K :=
  2+8*includeGaussian a + star (⟨1,1⟩ : GaussianFrame.G K)*(8*includeGaussian b) +
    star (⟨c.val,2⟩ : GaussianFrame.G K)*(8*includeGaussian d)

theorem small_pivot_unit (u v : D) :
    IsUnit (⟨2+8*u.val,8*v.val⟩ : GaussianFrame.G K) := by
  have h8 (z : D) : ‖(8:K)*z.val‖ ≤ 1/8 := by
    rw [show (8:K)=2^3 by norm_num,norm_mul,norm_scale]
    norm_num
    linarith [(mem_D _).mp z.2]
  have hn : ‖(2:K)+8*u.val‖ = 1/2 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_two]; linarith [h8 u]),
      norm_two,max_eq_left (by linarith [h8 u])]
  apply QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
  rw [isUnit_iff_ne_zero]
  change (2+8*u.val)*(2+8*u.val)+0*(2+8*u.val)*(8*v.val)-(-1)*(8*v.val)*(8*v.val) ≠ 0
  have h : (2+8*u.val)^2 + (8*v.val)^2 ≠ 0 := by
    intro h
    have he : (2+8*u.val)^2= -(8*v.val)^2 := eq_neg_of_add_eq_zero_left h
    have hh := congrArg (fun x : K => ‖x‖) he
    simp only [norm_neg,norm_pow,hn] at hh
    nlinarith [h8 v,norm_nonneg ((8:K)*v.val),sq_nonneg (1/8-‖(8:K)*v.val‖),
      mul_self_le_mul_self (norm_nonneg ((8:K)*v.val)) (h8 v)]
  convert h using 1 <;> ring

theorem original_patch_unit (c : D) (a b d : GInt) : IsUnit (framePivot c a b d) := by
  let u := a.re+b.re+b.im+c*d.re+2*d.im
  let v := a.im+b.im-b.re+c*d.im-2*d.re
  have h : framePivot c a b d = (⟨2+8*u.val,8*v.val⟩ : GaussianFrame.G K) := by
    ext <;> simp [framePivot,includeGaussian,u,v,QuadraticAlgebra.re_star,QuadraticAlgebra.im_star,
      QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat,QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul,show ((2:D):K)=2 by rfl] <;> ring
  rw [h]; exact small_pivot_unit u v

end FourChart
#print axioms FourChart.original_patch_unit
