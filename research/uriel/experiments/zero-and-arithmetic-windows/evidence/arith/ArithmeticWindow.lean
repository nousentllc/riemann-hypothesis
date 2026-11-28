import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow

open Set
namespace Uriel.ArithmeticWindow

/-- A common observable is bounded using a potentially different local index
at each ordinate. The two predicates at an ordinate agree on that index. -/
theorem selectedWindow
    {F : Deduction.CharFamily} {θ δ a xc xe xh : ℝ} {I : ℝ → Type}
    {E H : (y : ℝ) → I y → Prop} {S : Set ℝ}
    (ht : a ≤ θ)
    (supply : ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, Icc Y (Y ^ (1+δ)) ⊆ S)
    (explicit : ∀ y ≥ xe, ∀ i : I y, E y i)
    (core : ∀ y ≥ xc, y ∈ S → ∃ i : I y, H y i)
    (compare : ∀ y ≥ xh, ∀ i : I y, E y i → H y i → Deduction.Gm F y ≤ y ^ a) :
    ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ y ∈ Icc Y (Y ^ (1+δ)), Deduction.Gm F y ≤ 1 * y ^ θ := by
  intro Y₀
  obtain ⟨Y, hY, hS⟩ := supply (max Y₀ (max 1 (max xc (max xe xh))))
  refine ⟨Y, (le_max_left _ _).trans hY, ?_⟩
  intro y hy
  have hz := ((le_max_right _ _).trans hY).trans hy.1
  have hy1 := le_of_max_le_left hz
  have hthreshold := le_of_max_le_right hz
  have hx := le_of_max_le_right hthreshold
  obtain ⟨i, hi⟩ := core y (le_of_max_le_left hthreshold) (hS hy)
  rw [one_mul]
  exact (compare y (le_of_max_le_right hx) i (explicit y (le_of_max_le_left hx) i) hi).trans
    (Real.rpow_le_rpow_of_exponent_le hy1 ht)

/-- Conditional composition with the actual pinned analytic theorem. -/
theorem zeroFreeFromLocalHosts
    {F : Deduction.CharFamily} {θ δ a xc xe xh : ℝ} {I : ℝ → Type}
    {E H : (y : ℝ) → I y → Prop} {S : Set ℝ}
    (h0 : 0 < θ) (h1 : θ < 1) (hd : 0 < δ) (ht : a ≤ θ)
    (supply : ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, Icc Y (Y ^ (1+δ)) ⊆ S)
    (explicit : ∀ y ≥ xe, ∀ i : I y, E y i)
    (core : ∀ y ≥ xc, y ∈ S → ∃ i : I y, H y i)
    (compare : ∀ y ≥ xh, ∀ i : I y, E y i → H y i → Deduction.Gm F y ≤ y ^ a) :
    Deduction.ZeroFree F θ :=
  Deduction.zeroFree_of_rpow_window F (C := 1) h0 h1 hd
    (selectedWindow ht supply explicit core compare)

/-- Squared endpoint fit of the [kW,(kW)^(3/2)] subwindow. -/
theorem fitIff {k W : ℝ} (h : 0 < W) :
    (k*W)^3 ≤ W^4 ↔ k^3 ≤ W := by
  rw [mul_pow, show W^4 = W * W^3 by ring]
  exact mul_le_mul_iff_left₀ (pow_pos h _)

/-- The spare unit from the page cutoff 401 to the host cutoff 400. -/
theorem cutoffIff {k x : ℝ} (h : 0 < x) :
    (k*x)^400 ≤ x^401 ↔ k^400 ≤ x := by
  rw [mul_pow, show x^401 = x*x^400 by ring]
  exact mul_le_mul_iff_left₀ (pow_pos h _)

end Uriel.ArithmeticWindow

#print axioms Uriel.ArithmeticWindow.selectedWindow
#print axioms Uriel.ArithmeticWindow.zeroFreeFromLocalHosts
#print axioms Uriel.ArithmeticWindow.fitIff
#print axioms Uriel.ArithmeticWindow.cutoffIff
