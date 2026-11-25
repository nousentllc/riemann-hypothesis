import DilateBoundaryCore
import DilatePrimitive
import DilateLow

noncomputable section
namespace RamDilate

/-- Exact finite count over the zero residue at every coefficient depth
r ≥ 2. This concerns congruence vectors and does not assign a measure to the
singular fiber in the ambient local field. -/
theorem zero_residue (r : ℕ) (hr : 2≤r) :
    TargetOne.count 6 (0 : S r) = 2*den r := by
  apply Boundary.zero_counts (r := r)
  · exact low2_zero
  · exact low3_zero
  · exact low4_zero
  · intro m hm
    simpa only [mul_zero] using primitive_multiple m hm 0
  · exact hr

theorem below_cutoff {r k : ℕ} (hr : 2≤r) (h : r≤2*k) (u : S r) :
    TargetOne.count 6 ((4 : S r)^k*u^2)=2*den r :=
  Boundary.early h (zero_residue r hr) u

/-- At coefficient depth 2*k the finite quotient gives a strict shortfall,
for every k ≥ 1 and every unit digit (in fact, every digit). -/
theorem last_shortfall (k : ℕ) (hk : 1≤k) (u : S (2*k)) :
    256^k*TargetOne.count 6 ((4 : S (2*k))^k*u^2) <
      (2*256^k+2)*den (2*k) :=
  Boundary.strict u (zero_residue (2*k) (by omega))
end RamDilate
#print axioms RamDilate.last_shortfall
