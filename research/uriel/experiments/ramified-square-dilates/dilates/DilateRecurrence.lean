import DilateDefs
import RamBridge

noncomputable section
namespace RamDilate

/-- The exponent j counts the number of single divisions by 2 above the anchor 4.
The two subsidiary hypotheses refer to disjoint subtypes of the very same fiber. -/
theorem from_strata
    (primitive : ∀ n : ℕ, ∀ t : S (n+5), 8 * prim (n+5) (8*t) = 15 * den (n+5))
    (descent : ∀ r a : ℕ, imprim (r+1) ((2 : S (r+1)) * (a : S (r+1))) =
      64 * TargetOne.count 6 (a : S r))
    (base : ∀ n, 256*TargetOne.count 6 (4 : S (n+3)) = 514*den (n+3))
    (first : 4096*TargetOne.count 6 (8 : S 4) = 8194*den 4)
    (j n : ℕ) :
    16^(j+2) * TargetOne.count 6 (2^(j+2) : S (n+j+3)) =
      (2*16^(j+2)+2) * den (n+j+3) := by
  induction j with
  | zero =>
    simpa only [Nat.zero_add, Nat.add_zero, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd,
      show (2:S (n+3))^2=4 by norm_num] using base n
  | succ j ih =>
    by_cases hlow : n+j=0
    · obtain rfl : n=0 := by omega
      obtain rfl : j=0 := by omega
      norm_num only [Nat.reduceAdd,Nat.reducePow,Nat.reduceMul,show (2:S 4)^3=8 by norm_num]
      exact first
    let r := n+j+3
    have hdepth : n+(j+1)+3 = r+1 := by dsimp [r]; omega
    rw [hdepth]
    let a : ℕ := 2^(j+2)
    have hx : (2^(j+1+2) : S (r+1)) = 2 * (a : S (r+1)) := by
      dsimp [a]; push_cast; ring
    have hx8 : (2^(j+1+2) : S (r+1)) = 8 * (2^j : S (r+1)) := by ring
    have hp : 8*prim (r+1) (2^(j+1+2) : S (r+1)) = 15 * den (r+1) := by
      rw [hx8]
      have d : r+1 = (n+j-1)+5 := by dsimp [r]; omega
      rw [d]; exact primitive _ _
    have he : imprim (r+1) (2^(j+1+2) : S (r+1)) =
        64 * TargetOne.count 6 (2^(j+2) : S r) := by
      rw [hx,descent]; simp [a]
    rw [split, show (16^(j+1+2) : ℕ) = 16*16^(j+2) by ring]
    calc
      _ = 16*(16^(j+2)*imprim (r+1) (2^(j+1+2))) +
          (2*16^(j+2))*(8*prim (r+1) (2^(j+1+2))) := by ring
      _ = 1024*(16^(j+2)*TargetOne.count 6 (2^(j+2) : S r)) +
          (2*16^(j+2))*(15*den (r+1)) := by rw [he,hp]; ring
      _ = _ := by
        change 16^(j+2)*TargetOne.count 6 (2^(j+2) : S r) = (2*16^(j+2)+2)*den r at ih
        rw [ih,den_succ r]; ring

/-- Re-index the single-division recurrence at every positive square dilate. -/
theorem at_square
    (h : ∀ j n : ℕ, 16^(j+2) * TargetOne.count 6 (2^(j+2) : S (n+j+3)) =
      (2*16^(j+2)+2) * den (n+j+3))
    (k : ℕ) (hk : 1 ≤ k) :
    ∀ n : ℕ, 256^k * TargetOne.count 6 (4^k : S (n+(2*k+1))) =
      (2*256^k+2)*den (n+(2*k+1)) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  intro n
  rw [show 2*(m+1)+1 = 2*m+3 by omega]
  rw [← Nat.add_assoc]
  have hp (x : ℕ) : (16^(2*x+2) : ℕ) = 256^(x+1) := by
    rw [show 2*x+2 = 2*(x+1) by omega,pow_mul]; norm_num
  have ht : (2^(2*m+2) : S (n+2*m+3)) = 4^(m+1) := by
    rw [show 2*m+2 = 2*(m+1) by omega,pow_mul]; norm_num
  simpa only [hp,ht] using h (2*m) n

end RamDilate
