import DilateDescent

/-! The finite zero residue remains distinguishable from the eventual normalized
mass at the last precision that does not see the square target. -/
noncomputable section
namespace RamDilate.Boundary

/-- The zero residue has exactly the fixed-point count at all integer
coefficient precisions from two on. The recurrence fixes this number because
15/8 + (1/16)*2 = 2. -/
theorem zero_counts
    (low2 : TargetOne.count 6 (0 : S 2)=2*den 2)
    (low3 : TargetOne.count 6 (0 : S 3)=2*den 3)
    (low4 : TargetOne.count 6 (0 : S 4)=2*den 4)
    (primitive : ∀ r : ℕ, 5≤r → 8*prim r 0=15*den r)
    (r : ℕ) (hr : 2≤r) : TargetOne.count 6 (0 : S r)=2*den r := by
  have high (n : ℕ) : TargetOne.count 6 (0 : S (n+4))=2*den (n+4) := by
    induction n with
    | zero => exact low4
    | succ n ih =>
      change TargetOne.count 6 (0 : S ((n+4)+1)) = 2*den ((n+4)+1)
      have h := imprim_double_nat (n+4) 0
      simp only [Nat.cast_zero,mul_zero] at h
      have p := primitive ((n+4)+1) (by omega)
      rw [ih] at h
      rw [den_succ (n+4)] at p ⊢
      rw [split,h]
      omega
  by_cases h : 4≤r
  · exact (show r=(r-4)+4 by omega) ▸ high (r-4)
  · rcases (show r=2 ∨ r=3 by omega) with h|h <;> subst r <;> assumption

/-- At and below its exponent, the target reduces to zero, even though the
element of the local field itself is nonzero. -/
theorem target_eq_zero {r k : ℕ} (h : r≤2*k) : (4 : S r)^k=0 := by
  have d : 2^r ∣ (4:ℕ)^k := by
    rw [show (4:ℕ)^k=2^(2*k) by rw [pow_mul]; norm_num]
    exact pow_dvd_pow 2 h
  have z : (((4:ℕ)^k : ℕ) : ZMod (2^r))=0 := (ZMod.natCast_eq_zero_iff ..).mpr d
  simpa only [Nat.cast_pow,Nat.cast_ofNat,map_pow,map_ofNat,map_zero] using
    congrArg (algebraMap (ZMod (2^r)) (S r)) z

/-- Every scalar unit twist has the same zero residue at these resolutions. -/
theorem early {r k : ℕ} (h : r≤2*k)
    (hz : TargetOne.count 6 (0 : S r) = 2*den r) (u : S r) :
    TargetOne.count 6 ((4 : S r)^k*u^2)=2*den r := by
  rw [target_eq_zero h,zero_mul,hz]

/-- Strict discrepancy from the eventual prediction at the last precision
where the residue is zero. -/
theorem strict {k : ℕ} (u : S (2*k))
    (hz : TargetOne.count 6 (0 : S (2*k)) = 2*den (2*k)) :
    256^k*TargetOne.count 6 ((4 : S (2*k))^k*u^2) <
      (2*256^k+2)*den (2*k) := by
  rw [early (le_refl _) hz u,Nat.add_mul]
  have hd : 0 < den (2*k) := by unfold den; positivity
  rw [show 256^k*(2*den (2*k))=(2*256^k)*den (2*k) by ring]
  omega
end RamDilate.Boundary
