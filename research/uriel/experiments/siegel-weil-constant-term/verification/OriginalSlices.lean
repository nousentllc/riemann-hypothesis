import Mathlib

noncomputable section
open Filter MeasureTheory
open scoped Matrix Topology Classical

namespace PositivityTheory.SiegelWeilFormula.Gen.W

theorem euler_prod {ι : Type} (q : ι → ℕ) (hq : ∀ v, 2 ≤ q v) (hs : ∀ s : ℝ, 1 < s → Summable fun v => (q v : ℝ) ^ (-s))
    (c : ι → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) (k : ℕ) : ∃ d : ℂ → ℂ, DifferentiableOn ℂ d {z | 0 < z.re} ∧ ∀ z : ℂ, 0 < z.re →
      HasProd (fun v => 1 - c v * (q v : ℂ) ^ (-(2 * z + (k + 1 : ℕ)))) (d z) := by
  let x : ι → ℂ → ℂ := fun v z => -(c v * (q v : ℂ) ^ (-(2 * z + (k + 1 : ℕ))))
  have h1 : ∀ v, (1 : ℝ) ≤ q v := fun v => by exact_mod_cast one_le_two.trans (hq v)
  have hx : ∀ v z (t : ℝ), t ≤ 2 * z.re + 1 → ‖x v z‖ ≤ (q v : ℝ) ^ (-t) := fun v z t ht => by
    rw [norm_neg, norm_mul, Complex.norm_natCast_cpow_of_pos (two_pos.trans_le (hq v))]
    refine (mul_le_of_le_one_left (by positivity) (hc v)).trans (Real.rpow_le_rpow_of_exponent_le (h1 v) ?_)
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]
    push_cast
    linarith
  have hh : ∀ v z, 0 < z.re → ‖x v z‖ ≤ 1 / 2 := fun v z hz => by
    refine (hx v z 1 (by linarith)).trans ?_
    rw [Real.rpow_neg_one, one_div]
    exact inv_anti₀ two_pos (by exact_mod_cast hq v)
  have hb : ∀ v z (t : ℝ), 0 < z.re → t ≤ 2 * z.re + 1 → ‖Complex.log (1 + x v z)‖ ≤ 3 / 2 * (q v : ℝ) ^ (-t) :=
    fun v z t hz ht => (Complex.norm_log_one_add_half_le_self (hh v z hz)).trans (by gcongr; exact hx v z t ht)
  have hsl : ∀ v z, 0 < z.re → 1 + x v z ∈ Complex.slitPlane := fun v z hz =>
    Complex.mem_slitPlane_of_norm_lt_one ((hh v z hz).trans_lt (by norm_num))
  refine ⟨fun z => Complex.exp (∑' v, Complex.log (1 + x v z)), fun z hz => ?_, fun z hz => ?_⟩
  · have hz' : 0 < z.re := hz
    have ho : IsOpen {w : ℂ | z.re / 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have := Complex.differentiableOn_tsum_of_summable_norm (F := fun v w => Complex.log (1 + x v w))
      ((hs (z.re + 1) (by linarith)).mul_left (3 / 2)) (fun v w hw => ?_) ho
      fun v w (hw : z.re / 2 < w.re) => hb v w _ (by linarith) (by linarith)
    · exact (this.differentiableAt (ho.mem_nhds (show z.re / 2 < z.re by linarith))).cexp.differentiableWithinAt
    · have hw' : z.re / 2 < w.re := hw
      have hw0 : 0 < w.re := by linarith
      refine (DifferentiableAt.clog (f := fun w => 1 + x v w) ?_ (hsl v w hw0)).differentiableWithinAt
      have : (q v : ℂ) ≠ 0 := by exact_mod_cast (two_pos.trans_le (hq v)).ne'
      exact (((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => -(2 * z + (k + 1 : ℕ))) w).const_cpow
        (Or.inl this)).const_mul _).neg.const_add _
  · have := (Summable.of_norm_bounded ((hs (2 * z.re + 1) (by linarith)).mul_left (3 / 2))
      fun v => hb v z _ hz le_rfl).hasSum.cexp
    convert this using 2 with v
    rw [Function.comp_apply, Complex.exp_log (Complex.slitPlane_ne_zero (hsl v z hz)), sub_eq_add_neg]

def unrP (n M : ℕ) (e : ℤˣ) (q : ℕ) (z : ℂ) : ℂ :=
  ∏ i : Fin n, (1 - ((e : ℤ) : ℂ) ^ (M + (i : ℕ)) * (q : ℂ) ^ (-(2 * z + n - (i : ℕ))))

theorem unramifiedPart_differentiable (n M : ℕ) (e : ℤˣ) (q : ℕ) (hq : q ≠ 0) : Differentiable ℂ (unrP n M e q) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  unfold unrP
  refine Differentiable.fun_finsetProd fun i _ => ?_
  exact (differentiable_const _).sub ((differentiable_const _).mul
    ((by fun_prop : Differentiable ℂ (fun z : ℂ => -(2 * z + n - (i : ℕ)))).const_cpow (Or.inl hq')))

theorem norm_unit_pow (e : ℤˣ) (k : ℕ) : ‖((e : ℤ) : ℂ) ^ k‖ ≤ 1 := by
  rcases Int.units_eq_one_or e with h | h <;> simp [h]

theorem eq_of_eqOn_right {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (t : ℝ)
    (h : ∀ z : ℂ, t < z.re → f z = g z) : f = g := by
  have ho : IsOpen {w : ℂ | t < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hz : ((t + 1 : ℝ) : ℂ) ∈ {w : ℂ | t < w.re} := by simp
  have hev : f =ᶠ[nhds ((t + 1 : ℝ) : ℂ)] g := Filter.eventually_of_mem (ho.mem_nhds hz) fun w hw => h w hw
  have := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (f := f) (g := g) (U := Set.univ)
    (fun z _ => hf.analyticAt z) (fun z _ => hg.analyticAt z) isPreconnected_univ (Set.mem_univ _) hev
  funext z
  exact this (Set.mem_univ z)

theorem hasProd_split {α : Type} (f : α → ℂ) (S : Finset α) (D : ℂ)
    (h : HasProd (fun v : ↥((↑S : Set α)ᶜ) => f v) D) : HasProd f ((∏ v ∈ S, f v) * D) := by
  have ha : HasProd (fun v : ↥(↑S : Set α) => f v) (∏ v ∈ S, f v) := by
    convert hasProd_fintype (fun v : ↥(↑S : Set α) => f v) using 1
    exact (Finset.prod_coe_sort S f).symm
  exact ha.mul_compl h

end PositivityTheory.SiegelWeilFormula.Gen.W

namespace PositivityTheory.SiegelWeilFormula.Gen.WQ
open PositivityTheory.SiegelWeilFormula.Gen.W

def unrX (N M : ℕ) (c : ℂ) (q : ℕ) (z : ℂ) : ℂ :=
  ∏ i : Fin N, (1 - c ^ (M + (i : ℕ)) * (q : ℂ) ^ (-(2 * z + N - (i : ℕ))))

theorem unrX_differentiable (N M : ℕ) (c : ℂ) (q : ℕ) (hq : q ≠ 0) : Differentiable ℂ (unrX N M c q) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  unfold unrX
  refine Differentiable.fun_finsetProd fun i _ => ?_
  exact (differentiable_const _).sub ((differentiable_const _).mul
    ((by fun_prop : Differentiable ℂ (fun z : ℂ => -(2 * z + N - (i : ℕ)))).const_cpow (Or.inl hq')))

theorem hasProd_split' {α : Type} (f : α → ℂ) (S : Finset α) (D : ℂ)
    (h : HasProd (fun v : {v // v ∉ S} => f v) D) : HasProd f ((∏ v ∈ S, f v) * D) :=
  hasProd_split f S D h

theorem fix_point (Z H : ℂ → ℂ) (j : ℂ) (hZ : MeromorphicOn Z Set.univ) (hH : AnalyticAt ℂ H j)
    (he : ∀ᶠ s in 𝓝[≠] j, H s = Z s) :
    MeromorphicOn (Function.update Z j (H j)) Set.univ ∧ AnalyticAt ℂ (Function.update Z j (H j)) j ∧
      Function.update Z j (H j) j = H j ∧ ∀ s, s ≠ j → Function.update Z j (H j) s = Z s := by
  refine ⟨fun z _ => (hZ z trivial).update _ _, ?_, by simp, fun s hs => Function.update_of_ne hs _ _⟩
  refine hH.congr (eventuallyEq_nhds_of_eventuallyEq_nhdsNE ?_ (by simp))
  filter_upwards [he, self_mem_nhdsWithin] with s hs hs'
  rw [Function.update_of_ne (show s ≠ j from hs'), hs]

theorem pow_sub_of_sq (c : ℂ) (hc : c ^ 2 = 1) (N i : ℕ) (hi : i ≤ N) :
    c ^ (N + i) = c ^ (((N - i : ℕ) : ℤ)) := by
  rw [zpow_natCast]
  have : N + i = (N - i) + 2 * i := by omega
  rw [this, pow_add, pow_mul, hc, one_pow, mul_one]

theorem mul_div_cancel_of_eq (x y D : ℂ) (hD : D ≠ 0) (hy : y = D) : x * y / D = x := by
  subst hy; field_simp

theorem unrX_zero_split (m : ℕ) (c : ℂ) (hc : c ^ 2 = 1) (q : ℕ) (hne : 1 - c / q ≠ 0) :
    unrX (m + 1) (m + 1) c q 0 / (1 - c / q) =
      ∏ i : Fin m, (1 - c ^ (((m + 1 - (i : ℕ) : ℕ)) : ℤ) * (q : ℂ) ^ (-(((m + 1 - (i : ℕ) : ℕ)) : ℂ))) := by
  unfold unrX
  rw [Fin.prod_univ_castSucc, mul_div_cancel_of_eq _ _ _ hne]
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Fin.val_castSucc]
    rw [pow_sub_of_sq c hc (m + 1) i (by omega)]
    congr 3
    rw [Nat.cast_sub (by omega : (i : ℕ) ≤ m + 1)]
    push_cast
    ring
  · simp only [Fin.val_last]
    rw [pow_sub_of_sq c hc (m + 1) m (by omega)]
    have h1 : m + 1 - m = 1 := by omega
    rw [h1]
    push_cast
    rw [show -(2 * (0 : ℂ) + (m + 1) - m) = -1 by ring, Complex.cpow_neg_one, zpow_one, div_eq_mul_inv]

end PositivityTheory.SiegelWeilFormula.Gen.WQ

namespace PositivityTheory.SiegelWeilFormula.Gen.WL

theorem det_mul_eq_zero_of_lt {R : Type*} [CommRing R] {M n : ℕ} (h : M < n)
    (X : Matrix (Fin n) (Fin M) R) (Y : Matrix (Fin M) (Fin n) R) : (X * Y).det = 0 := by
  let e : Matrix (Fin M) (Fin n) R := Matrix.of fun i k => if Fin.castLE h.le i = k then 1 else 0
  have he : e * eᵀ = 1 := by
    ext i j
    simp only [e, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Fin.castLE_inj, eq_comm (a := j)]
  have : X * Y = (X * e) * (eᵀ * Y) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc e, he, Matrix.one_mul]
  rw [this, Matrix.det_mul, Matrix.det_eq_zero_of_column_eq_zero (A := X * e) ⟨M, h⟩, zero_mul]
  intro a
  simp only [Matrix.mul_apply, e, Matrix.of_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [if_neg, mul_zero]
  intro hh
  have := congrArg Fin.val hh
  simp at this
  omega

theorem count (c d M n : ℕ) (hd : 1 ≤ d) (h : M < n) :
    (∑ i : Fin n, (if 1 ≤ (M : ℤ) - ((i : ℕ) : ℤ) then 0 else if (M : ℤ) - ((i : ℕ) : ℤ) = 0 then c + d - 1 else d)) + 1
      = d * (n - M) + c := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    if 1 ≤ (M : ℤ) - (i : ℤ) then 0 else if (M : ℤ) - (i : ℤ) = 0 then c + d - 1 else d) n]
  obtain ⟨r, rfl⟩ : ∃ r, n = M + 1 + r := ⟨n - M - 1, by omega⟩
  clear h
  induction r with
  | zero =>
    rw [Nat.add_zero, Finset.sum_range_succ, Finset.sum_eq_zero fun i hi => by
      have := Finset.mem_range.1 hi
      rw [if_pos (by omega)]]
    rw [if_neg (by omega), if_pos (by omega)]
    have : M + 1 - M = 1 := by omega
    rw [this, mul_one]
    omega
  | succ r ih =>
    rw [show M + 1 + (r + 1) = M + 1 + r + 1 by ring, Finset.sum_range_succ, add_right_comm, ih]
    rw [if_neg (by omega), if_neg (by omega)]
    have : M + 1 + r + 1 - M = (M + 1 + r - M) + 1 := by omega
    rw [this, Nat.mul_succ]
    ring

theorem analyticAt_update_zero {G A : ℂ → ℂ} {s₀ c : ℂ} {K N : ℕ} (hc : c ≠ 0) (hKN : K < N)
    (hA : AnalyticAt ℂ A s₀) (h : ∀ᶠ z in 𝓝[≠] s₀, c * (z - s₀) ^ K * G z = (z - s₀) ^ N * A z) :
    AnalyticAt ℂ (fun z => if z = s₀ then 0 else G z) s₀ := by
  have hB : AnalyticAt ℂ (fun z => c⁻¹ * ((z - s₀) ^ (N - K) * A z)) s₀ :=
    analyticAt_const.mul ((by fun_prop : AnalyticAt ℂ (fun z : ℂ => (z - s₀) ^ (N - K)) s₀).mul hA)
  refine hB.congr ?_
  filter_upwards [eventually_nhdsWithin_iff.1 h] with z hz
  by_cases hzs : z = s₀
  · subst hzs
    rw [if_pos rfl, sub_self, zero_pow (by omega), zero_mul, mul_zero]
  · rw [if_neg hzs]
    have hx : z - s₀ ≠ 0 := sub_ne_zero.2 hzs
    have h1 := hz hzs
    have hN : (z - s₀) ^ N = (z - s₀) ^ K * (z - s₀) ^ (N - K) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hN] at h1
    have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
    apply mul_left_cancel₀ (mul_ne_zero hc (pow_ne_zero K hx))
    rw [h1]
    linear_combination ((z - s₀) ^ K * (z - s₀) ^ (N - K) * A z) * hcc

end PositivityTheory.SiegelWeilFormula.Gen.WL
end
