import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace DensityGate

/-- A necessary retained-density condition for the saturated scalar envelope. -/
theorem necessary (x L m dt d2 S : ℝ)
    (hx : 0 < x) (hL : 0 < L) (hm : 0 < m) (ht : 0 < dt) (hd : 0 < d2)
    (hs : 2*x/(m*d2) + 4*m*L/(dt*d2) ≤ S)
    (budget : L^5*S + 4/(x*d2) ≤ Real.sqrt x*(L^8-4*L)) :
    32*L^11 < dt*d2^2*(L^8-4*L)^2 := by
  let a : ℝ := 2*x/(m*d2)
  let b : ℝ := 4*m*L/(dt*d2)
  change a+b ≤ S at hs
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hleft : 0 ≤ L^5*(a+b) := by positivity
  have step : L^5*(a+b) < Real.sqrt x*(L^8-4*L) :=
    calc L^5*(a+b) ≤ L^5*S := mul_le_mul_of_nonneg_left hs (by positivity)
         _ < L^5*S+4/(x*d2) := lt_add_of_pos_right _ (by positivity)
         _ ≤ _ := budget
  have am : 4*(a*b) ≤ (a+b)^2 := by nlinarith [sq_nonneg (a-b)]
  have hh : 4*(a*b)*L^10 < x*(L^8-4*L)^2 :=
    calc 4*(a*b)*L^10 ≤ (a+b)^2*L^10 := mul_le_mul_of_nonneg_right am (by positivity)
         _ = (L^5*(a+b))^2 := by ring
         _ < (Real.sqrt x*(L^8-4*L))^2 := by
           simpa only [pow_two] using mul_self_lt_mul_self hleft step
         _ = x*(L^8-4*L)^2 := by rw [mul_pow, Real.sq_sqrt hx.le]
  have ident : (4*(a*b)*L^10)*(dt*d2^2) = 32*x*L^11 := by
    dsimp [a,b]
    field_simp
    ring
  have both := mul_lt_mul_of_pos_right hh (by positivity : 0 < dt*d2^2)
  rw [ident] at both
  apply (mul_lt_mul_iff_right₀ hx).mp
  calc x * (32*L^11) = 32*x*L^11 := by ring
       _ < (x*(L^8-4*L)^2)*(dt*d2^2) := both
       _ = x*(dt*d2^2*(L^8-4*L)^2) := by ring
#print axioms necessary

/-- Apply the threshold to the complete normalized bracket with both additive losses. -/
theorem full_envelope (x L m k n dt d2 : ℝ)
    (hx : 0 < x) (hL : 0 < L) (hm : 0 < m) (hk : 0 < k) (hn : 0 < n)
    (ht : 0 < dt) (hd : 0 < d2)
    (h : L^5*(2*x/(m*d2)*(1 + m^2/k) + 4*m*L/(dt*d2) + 2*k*L^2/(dt*n^2))
          + 4/(x*d2) + 4*Real.sqrt x*L ≤ Real.sqrt x*L^8) :
    32*L^11 < dt*d2^2*(L^8-4*L)^2 := by
  apply necessary x L m dt d2 _ hx hL hm ht hd _ (by linarith [h] :
    L^5*(2*x/(m*d2)*(1 + m^2/k) + 4*m*L/(dt*d2) + 2*k*L^2/(dt*n^2))
      + 4/(x*d2) ≤ Real.sqrt x*(L^8-4*L))
  have hcross : 0 ≤ 2*x/(m*d2)*(m^2/k) := by positivity
  have hlast : 0 ≤ 2*k*L^2/(dt*n^2) := by positivity
  linarith only [hcross, hlast]

#print axioms full_envelope
end DensityGate
