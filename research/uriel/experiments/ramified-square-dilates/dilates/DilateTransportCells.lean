import RamPlaceEndpoint

open MeasureTheory Topology
open scoped ENNReal
noncomputable section
namespace DilateTransport

/-- The scalar count must hold on a cofinal tail. The cutoff may depend on the target. -/
abbrev countsAt (k : ℕ) := ∃ r0 : ℕ, ∀ n : ℕ,
  256^k * TargetOne.count 6 (4^k : RamField.R (n+r0)) =
    (2*256^k+2) * (((2^(n+r0))^2)^5)

open RamField

/-- Coefficient cylinders around any integral target, with an arbitrarily prescribed
starting depth, refine all its neighborhoods in the completed field. -/
theorem small (a : O) (r0 : ℕ) (N : Set K) (hN : N ∈ 𝓝 (inc a)) :
    ∃ n : ℕ, cylinder (n+r0) (digit (n+r0) a) ⊆ N := by
  have pre : pairInc ⁻¹' N ∈ 𝓝 (a.re,a.im) :=
    pairInc_openEmbedding.continuous.continuousAt (by exact hN)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp pre
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2:ℝ)⁻¹ < 1)
  have hr : (2:ℝ)^(-((n+r0:ℕ):ℤ)) < ε := by
    rw [zpow_neg,zpow_natCast,←inv_pow]
    exact lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : n≤n+r0)) hn
  refine ⟨n,?_⟩
  rintro _ ⟨y,hy,rfl⟩
  change digit (n+r0) y = digit (n+r0) a at hy
  have hb1 : y.re ∈ Metric.closedBall a.re ((2:ℝ)^(-((n+r0:ℕ):ℤ))) := by
    rw [← TargetOne.ball_digit]
    exact congrArg QuadraticAlgebra.re hy
  have hb2 : y.im ∈ Metric.closedBall a.im ((2:ℝ)^(-((n+r0:ℕ):ℤ))) := by
    rw [← TargetOne.ball_digit]
    exact congrArg QuadraticAlgebra.im hy
  apply hball (a := (y.re,y.im))
  exact max_lt ((Metric.mem_closedBall.mp hb1).trans_lt hr)
    ((Metric.mem_closedBall.mp hb2).trans_lt hr)

/-- Clear denominators in the finite cylinder ratio, keeping the measure itself
in the extended nonnegative reals. -/
private theorem scaledRatio (k n q : ℕ) (hq : q ≠ 0)
    (h : 256^k*n = (2*256^k+2)*q^5) :
    (n:ℝ≥0∞)*(1/(q:ℝ≥0∞))^6 = (2+2/256^k:ℝ≥0∞)*(1/(q:ℝ≥0∞)) := by
  have hn : (256:ℝ)^k*n = (2*(256:ℝ)^k+2)*(q:ℝ)^5 := by exact_mod_cast h
  have hq' : (q:ℝ) ≠ 0 := by exact_mod_cast hq
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_natCast,
    ENNReal.toReal_add (a := 2) (b := 2/256^k) (by finiteness) (by finiteness),ENNReal.toReal_one,ENNReal.toReal_ofNat]
  field_simp
  linarith

/-- Every integral unit stays a unit in every quotient. Multiplication of the
six coordinates by that residue unit gives an exact permutation of solutions. -/
theorem unit_count (k r : ℕ) (u : Oˣ) :
    TargetOne.count 6 (digit r ((4:O)^k*(u:O)^2)) = TargetOne.count 6 (4^k : R r) := by
  rw [map_mul,map_pow,map_pow,map_ofNat,mul_comm]
  exact TargetFour.scaled (Units.map (digit r).toMonoidHom u) _

theorem tube (k r : ℕ) (u : Oˣ) (lam : Measure K) [lam.IsAddHaarMeasure]
    (hvol : lam integers = 1) (hcount : 256^k * TargetOne.count 6 (4^k : R r) =
      (2*256^k+2)*(((2^r)^2)^5)) :
    let C := cylinder r (digit r ((4:O)^k * (u:O)^2))
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers C) =
      (2+2/256^k : ℝ≥0∞) * lam C := by
  classical
  obtain ⟨i1,i2,i3,i4,-⟩ := id locally
  let : Fintype (R r) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  let q := (2^r : ℕ)^2
  have hm (b : R r) : lam (RamTransport.residueCell inc (digit r) b) = 1/(q:ℝ≥0∞) := by
    change lam (cylinder r b) = _
    simpa only [q,Nat.cast_pow,Nat.cast_ofNat] using cyl_mass lam hvol r b
  have hm' (b : R r) : MeasurableSet (RamTransport.residueCell inc (digit r) b) :=
    (open_cylinder r b).measurableSet
  have count_u := hcount
  rw [←unit_count k r u] at count_u
  exact (RamTransport.fiber_count_to_tube inc inc_injective (digit r) lam hm' _ hm _).trans
    ((scaledRatio k _ q (by dsimp [q]; positivity) count_u).trans
      (congrArg (_ * ·) (hm _).symm))

end DilateTransport
#print axioms DilateTransport.tube
