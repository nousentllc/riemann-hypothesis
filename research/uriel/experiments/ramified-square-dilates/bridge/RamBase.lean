import RamBaseTables

namespace RamBase
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem zeroCheck : checks (fun k =>
    decide ((if decode k = 0 then 1 else 0 : ℕ) = row0 (repNo k))) 1024 = true := by
  decide +kernel

theorem census_zero (z : R) : TargetOne.count 0 z = row0 (repNo (encode z)) := by
  rw [TargetOne.count_zero]
  have h := of_decide_eq_true (select zeroCheck (encode z) (encode_lt z))
  simpa only [decode_encode] using h

private theorem next {d : ℕ} {a b : ℕ → ℕ}
    (prev : ∀ z : R, TargetOne.count d z = a (repNo (encode z)))
    (cert : checks (fun k => decide (step (fun j => a (repNo j)) (encode (decode (repCode k))) = b k)) 58 = true)
    (z : R) : TargetOne.count (d+1) z = b (repNo (encode z)) := by
  have hh := of_decide_eq_true (select allOrbits (encode z) (encode_lt z))
  have hc := of_decide_eq_true (select cert (repNo (encode z)) hh.1)
  rw [reduce_to_rep, count_step d (fun t => a (repNo t)) prev]
  exact hc

theorem census_six (z : R) : TargetOne.count 6 z = row6 (repNo (encode z)) := by
  exact next (next (next (next (next (next census_zero transition0) transition1) transition2)
    transition3) transition4) transition5 z

theorem count_four : TargetOne.count 6 (4 : QuadraticAlgebra (ZMod 32) 2 0) = 257 * 2^43 := by
  rw [census_six]
  decide +kernel
end RamBase
#print axioms RamBase.count_four
