import Mathlib

namespace FormalAuditPanel

def packetGraph (edges : Finset (ℕ × ℕ)) : SimpleGraph ℕ where
  Adj a b := a ≠ b ∧ ((a,b) ∈ edges ∨ (b,a) ∈ edges)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩


theorem unions_V : (({0,2,3} : Finset ℕ) ∪ ({1,3} : Finset ℕ)).card ≥ 3 := by decide

theorem unions_S : (({0,2,3} : Finset ℕ) ∪ ({0,2} : Finset ℕ)).card ≥ 3 := by decide

theorem unions_K : (({1,2,3} : Finset ℕ) ∪ ({0,2,3} : Finset ℕ)).card ≥ 3 := by decide

theorem unions_P : ¬ ((({3} : Finset ℕ) ∪ ({2} : Finset ℕ)).card ≥ 3) := by decide

theorem unions_J : (({3} : Finset ℕ) ∪ ({1,2} : Finset ℕ)).card ≥ 3 := by decide

theorem unions_G : ¬ ((({2} : Finset ℕ) ∪ ({0} : Finset ℕ)).card ≥ 3) := by decide

theorem determinants_J : Matrix.det (!![3,1;3,1] : Matrix (Fin 2) (Fin 2) ℤ) = 0 := by norm_num [Matrix.det_fin_two]

theorem determinants_S : ¬ (Matrix.det (!![3,1;3,3] : Matrix (Fin 2) (Fin 2) ℤ) = 0) := by norm_num [Matrix.det_fin_two]

theorem determinants_K : ¬ (Matrix.det (!![2,1;2,4] : Matrix (Fin 2) (Fin 2) ℤ) = 0) := by norm_num [Matrix.det_fin_two]

theorem determinants_P : ¬ (Matrix.det (!![2,4;3,2] : Matrix (Fin 2) (Fin 2) ℤ) = 0) := by norm_num [Matrix.det_fin_two]

theorem determinants_G : ¬ (Matrix.det (!![2,1;1,4] : Matrix (Fin 2) (Fin 2) ℤ) = 0) := by norm_num [Matrix.det_fin_two]

theorem neighbors_P : 1 ∈ (packetGraph ({(0,1),(1,2),(1,4),(2,3)} : Finset (ℕ × ℕ))).commonNeighbors 0 2 := by simp [SimpleGraph.mem_commonNeighbors, packetGraph] <;> decide

theorem neighbors_S : ¬ (1 ∈ (packetGraph ({(0,1),(1,4),(2,3),(3,4)} : Finset (ℕ × ℕ))).commonNeighbors 0 2) := by simp [SimpleGraph.mem_commonNeighbors, packetGraph] <;> decide

theorem neighbors_V : 1 ∈ (packetGraph ({(0,1),(1,2),(2,3),(2,4)} : Finset (ℕ × ℕ))).commonNeighbors 0 2 := by simp [SimpleGraph.mem_commonNeighbors, packetGraph] <;> decide

theorem neighbors_G : ¬ (1 ∈ (packetGraph ({(0,4),(1,2)} : Finset (ℕ × ℕ))).commonNeighbors 0 2) := by simp [SimpleGraph.mem_commonNeighbors, packetGraph] <;> decide

theorem neighbors_K : 1 ∈ (packetGraph ({(0,1),(1,2)} : Finset (ℕ × ℕ))).commonNeighbors 0 2 := by simp [SimpleGraph.mem_commonNeighbors, packetGraph] <;> decide

theorem neighbors_J : ¬ (1 ∈ (packetGraph ({(0,4),(1,4)} : Finset (ℕ × ℕ))).commonNeighbors 0 2) := by simp [SimpleGraph.mem_commonNeighbors, packetGraph] <;> decide

theorem quadratics_K : ¬ (∃! x : ℚ, (3:ℚ) * (x*x) + (-4:ℚ)*x + (1:ℚ)=0) := by rw [← discrim_eq_zero_iff (a:=(3:ℚ)) (b:=(-4:ℚ)) (c:=(1:ℚ)) (by norm_num)]; norm_num [discrim]

theorem quadratics_V : ∃! x : ℚ, (3:ℚ) * (x*x) + (-6:ℚ)*x + (3:ℚ)=0 := by rw [← discrim_eq_zero_iff (a:=(3:ℚ)) (b:=(-6:ℚ)) (c:=(3:ℚ)) (by norm_num)]; norm_num [discrim]

theorem quadratics_J : ¬ (∃! x : ℚ, (3:ℚ) * (x*x) + (-4:ℚ)*x + (7:ℚ)=0) := by rw [← discrim_eq_zero_iff (a:=(3:ℚ)) (b:=(-4:ℚ)) (c:=(7:ℚ)) (by norm_num)]; norm_num [discrim]

theorem quadratics_P : ∃! x : ℚ, (2:ℚ) * (x*x) + (-4:ℚ)*x + (2:ℚ)=0 := by rw [← discrim_eq_zero_iff (a:=(2:ℚ)) (b:=(-4:ℚ)) (c:=(2:ℚ)) (by norm_num)]; norm_num [discrim]

theorem quadratics_S : ∃! x : ℚ, (2:ℚ) * (x*x) + (4:ℚ)*x + (2:ℚ)=0 := by rw [← discrim_eq_zero_iff (a:=(2:ℚ)) (b:=(4:ℚ)) (c:=(2:ℚ)) (by norm_num)]; norm_num [discrim]

theorem quadratics_G : ∃! x : ℚ, (2:ℚ) * (x*x) + (0:ℚ)*x + (0:ℚ)=0 := by rw [← discrim_eq_zero_iff (a:=(2:ℚ)) (b:=(0:ℚ)) (c:=(0:ℚ)) (by norm_num)]; norm_num [discrim]

theorem swaps_K : ¬ (Equiv.Perm.sign ((Equiv.swap (0:Fin 3) (0:Fin 3)) * (Equiv.swap (1:Fin 3) (1:Fin 3)) * (Equiv.swap (2:Fin 3) (2:Fin 3))) = -1) := by norm_num [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap'] <;> decide

theorem swaps_P : ¬ (Equiv.Perm.sign ((Equiv.swap (0:Fin 3) (0:Fin 3)) * (Equiv.swap (0:Fin 3) (0:Fin 3)) * (Equiv.swap (2:Fin 3) (2:Fin 3))) = -1) := by norm_num [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap'] <;> decide

theorem swaps_S : ¬ (Equiv.Perm.sign ((Equiv.swap (0:Fin 3) (2:Fin 3)) * (Equiv.swap (0:Fin 3) (0:Fin 3)) * (Equiv.swap (1:Fin 3) (2:Fin 3))) = -1) := by norm_num [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap'] <;> decide

theorem swaps_G : ¬ (Equiv.Perm.sign ((Equiv.swap (2:Fin 3) (2:Fin 3)) * (Equiv.swap (0:Fin 3) (2:Fin 3)) * (Equiv.swap (0:Fin 3) (1:Fin 3))) = -1) := by norm_num [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap'] <;> decide

theorem swaps_V : Equiv.Perm.sign ((Equiv.swap (2:Fin 3) (2:Fin 3)) * (Equiv.swap (0:Fin 3) (2:Fin 3)) * (Equiv.swap (0:Fin 3) (0:Fin 3))) = -1 := by norm_num [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap'] <;> decide

theorem swaps_J : Equiv.Perm.sign ((Equiv.swap (2:Fin 3) (2:Fin 3)) * (Equiv.swap (0:Fin 3) (2:Fin 3)) * (Equiv.swap (1:Fin 3) (1:Fin 3))) = -1 := by norm_num [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap'] <;> decide

theorem hamming_J : hammingDist (![1,0,0] : Fin 3 → ℕ) (![0,1,1] : Fin 3 → ℕ) = hammingDist (![1,0,0] : Fin 3 → ℕ) (![0,1,1] : Fin 3 → ℕ) + hammingDist (![0,1,1] : Fin 3 → ℕ) (![0,1,1] : Fin 3 → ℕ) := by decide

theorem hamming_K : ¬ (hammingDist (![0,1,0] : Fin 3 → ℕ) (![0,1,1] : Fin 3 → ℕ) = hammingDist (![0,1,0] : Fin 3 → ℕ) (![0,0,0] : Fin 3 → ℕ) + hammingDist (![0,0,0] : Fin 3 → ℕ) (![0,1,1] : Fin 3 → ℕ)) := by decide

theorem hamming_V : hammingDist (![0,1,0] : Fin 3 → ℕ) (![1,0,1] : Fin 3 → ℕ) = hammingDist (![0,1,0] : Fin 3 → ℕ) (![0,1,1] : Fin 3 → ℕ) + hammingDist (![0,1,1] : Fin 3 → ℕ) (![1,0,1] : Fin 3 → ℕ) := by decide

theorem hamming_P : hammingDist (![0,0,0] : Fin 3 → ℕ) (![1,0,1] : Fin 3 → ℕ) = hammingDist (![0,0,0] : Fin 3 → ℕ) (![1,0,1] : Fin 3 → ℕ) + hammingDist (![1,0,1] : Fin 3 → ℕ) (![1,0,1] : Fin 3 → ℕ) := by decide

theorem hamming_S : ¬ (hammingDist (![0,0,0] : Fin 3 → ℕ) (![1,1,0] : Fin 3 → ℕ) = hammingDist (![0,0,0] : Fin 3 → ℕ) (![1,0,1] : Fin 3 → ℕ) + hammingDist (![1,0,1] : Fin 3 → ℕ) (![1,1,0] : Fin 3 → ℕ)) := by decide

theorem hamming_G : hammingDist (![0,0,0] : Fin 3 → ℕ) (![1,0,1] : Fin 3 → ℕ) = hammingDist (![0,0,0] : Fin 3 → ℕ) (![1,0,0] : Fin 3 → ℕ) + hammingDist (![1,0,0] : Fin 3 → ℕ) (![1,0,1] : Fin 3 → ℕ) := by decide

theorem pairs_in_bins_V : ¬ (12 ≤ Nat.choose 4 2 + Nat.choose 2 2) := by decide

theorem pairs_in_bins_P : ¬ (12 ≤ Nat.choose 2 2 + Nat.choose 4 2) := by decide

theorem pairs_in_bins_G : ¬ (12 ≤ Nat.choose 2 2 + Nat.choose 3 2) := by decide

theorem pairs_in_bins_K : 12 ≤ Nat.choose 7 2 + Nat.choose 7 2 := by decide

theorem pairs_in_bins_J : ¬ (12 ≤ Nat.choose 5 2 + Nat.choose 1 2) := by decide

theorem pairs_in_bins_S : 12 ≤ Nat.choose 5 2 + Nat.choose 5 2 := by decide

theorem pair_encoding_P : Nat.pair 1 2 = Nat.pair 1 2 := by decide

theorem pair_encoding_G : ¬ (Nat.pair 1 1 = Nat.pair 1 2) := by decide

theorem pair_encoding_S : Nat.pair 0 1 = Nat.pair 0 1 := by decide

theorem pair_encoding_K : Nat.pair 0 0 = Nat.pair 0 0 := by decide

theorem pair_encoding_V : Nat.pair 0 2 = Nat.pair 0 2 := by decide

#print axioms unions_V

#print axioms unions_S

#print axioms unions_K

#print axioms unions_P

#print axioms unions_J

#print axioms unions_G

#print axioms determinants_J

#print axioms determinants_S

#print axioms determinants_K

#print axioms determinants_P

#print axioms determinants_G

#print axioms neighbors_P

#print axioms neighbors_S

#print axioms neighbors_V

#print axioms neighbors_G

#print axioms neighbors_K

#print axioms neighbors_J

#print axioms quadratics_K

#print axioms quadratics_V

#print axioms quadratics_J

#print axioms quadratics_P

#print axioms quadratics_S

#print axioms quadratics_G

#print axioms swaps_K

#print axioms swaps_P

#print axioms swaps_S

#print axioms swaps_G

#print axioms swaps_V

#print axioms swaps_J

#print axioms hamming_J

#print axioms hamming_K

#print axioms hamming_V

#print axioms hamming_P

#print axioms hamming_S

#print axioms hamming_G

#print axioms pairs_in_bins_V

#print axioms pairs_in_bins_P

#print axioms pairs_in_bins_G

#print axioms pairs_in_bins_K

#print axioms pairs_in_bins_J

#print axioms pairs_in_bins_S

#print axioms pair_encoding_P

#print axioms pair_encoding_G

#print axioms pair_encoding_S

#print axioms pair_encoding_K

#print axioms pair_encoding_V

end FormalAuditPanel
