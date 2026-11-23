import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open Formalism.L2.GlobalTheoryTheory GlobalTheory.EX
open scoped BigOperators

noncomputable section
namespace OrbitAudit


/-- When the order is below a full tile and both count caps dominate the order,
    every local configuration satisfies the actual good-orbit definition. -/
theorem every_arrangement_good (n : ℕ) (T : Finset (Fin n)) (L K r : ℕ) (d h x : ℝ)
    (hK : n ≤ K) (htile : n < (6 * r + 1) * G.goodU d)
    (hcap : n ≤ G.orbitWindowCount r d h x) :
    G.IsGoodOrbit n T L K r d h x := by
  have hsize : (T.map Fin.valEmbedding).card ≤ n := by
    simpa using (Finset.card_le_univ T)
  refine ⟨?_, ?_, ?_⟩
  · intro i _
    exact (Finset.card_le_card Finset.inter_subset_left).trans (hsize.trans hK)
  · intro s hs
    rw [Nat.div_eq_of_lt htile] at hs
    omega
  · intro i _
    exact (Finset.card_le_card Finset.inter_subset_left).trans (hsize.trans hcap)

/-- With exactly one complete tile, its markedness alone decides the tile clause,
    for every permitted look-ahead bound, including zero. -/
theorem one_tile_iff (n : ℕ) (T : Finset ℕ) (r u M : ℕ)
    (hone : n / ((6 * r + 1) * u) = 1) :
    Formalism.G0.CondTiles n T r u M ↔ Formalism.G0.Marked T r u 0 := by
  unfold Formalism.G0.CondTiles
  rw [hone]
  constructor
  · intro h
    obtain ⟨j, _, hj⟩ := h 0 (by decide)
    simpa only [Nat.mod_one] using hj
  · intro h s _
    exact ⟨0, Nat.zero_le _, by simpa only [Nat.mod_one] using h⟩

theorem good_one_tile_iff (n : ℕ) (T : Finset (Fin n)) (L K r : ℕ) (d h x : ℝ)
    (hone : n / ((6 * r + 1) * G.goodU d) = 1) :
    G.IsGoodOrbit n T L K r d h x ↔
      Formalism.G0.CondA n (T.map Fin.valEmbedding) L K ∧
      Formalism.G0.Marked (T.map Fin.valEmbedding) r (G.goodU d) 0 ∧
      Formalism.G0.CondIntervals n (T.map Fin.valEmbedding)
        (G.goodG' r d h x) (G.orbitWindowCount r d h x) := by
  unfold G.IsGoodOrbit Formalism.G0.GoodOrbitIntervalTileCondition
  rw [one_tile_iff _ _ _ _ _ hone]

open Formalism.G0

/-- A complete width-two tile is marked precisely when membership within it is
    the anchored residue pattern 2 modulo 4. This holds at every tile index. -/
theorem width_two_marked_iff (T : Finset ℕ) (r s : ℕ) :
    Marked T r 2 s ↔
      ∀ k < (6 * r + 1) * 2,
        s * ((6 * r + 1) * 2) + k ∈ T ↔ k % 4 = 2 := by
  let b := s * ((6 * r + 1) * 2)
  have beven : Even b := ⟨s * (6*r+1), by dsimp [b]; ring⟩
  rw [Nat.even_iff] at beven
  change Marked T r 2 s ↔ ∀ k < (6*r+1)*2, b+k ∈ T ↔ k % 4 = 2
  have hc (c z : ℕ) : z ∈ cell r 2 s c ↔ b+(c-1)*2 ≤ z ∧ z < b+c*2 :=
    Finset.mem_Ico
  constructor
  · intro h k hk
    let c := k / 2 + 1
    have hr : 1 ≤ c ∧ c ≤ 6*r+1 := by dsimp [c]; omega
    have hkc : b+k ∈ cell r 2 s c := (hc c _).mpr (by dsimp [c]; omega)
    obtain ⟨ho, he⟩ := h c hr.1 hr.2
    by_cases hev : Even c
    · obtain ⟨v, his, hv⟩ := he hev
      have hvI : v ∈ cell r 2 s c := (Finset.mem_inter.mp
        (his.symm ▸ (Finset.mem_singleton_self v))).2
      have hl := (hc c _).mp hvI
      have htest := (Finset.ext_iff.mp his) (b+k)
      simp only [Finset.mem_inter, hkc, and_true, Finset.mem_singleton] at htest
      rw [htest]
      rw [Nat.even_iff] at hev hv
      dsimp [c] at hl hev
      omega
    · have hod : Odd c := by simpa [Nat.not_even_iff_odd] using hev
      have hz := (Finset.ext_iff.mp (ho hod)) (b+k)
      simp only [Finset.mem_inter, hkc, and_true, Finset.notMem_empty, iff_false] at hz
      rw [Nat.odd_iff] at hod
      dsimp [c] at hod
      have hneq : k % 4 ≠ 2 := by omega
      exact iff_of_false hz hneq
  · intro h c hlo hhi
    have hread (z : ℕ) (hz : z ∈ cell r 2 s c) :
        z ∈ T ↔ (z-b)%4 = 2 := by
      have hl := (hc c z).mp hz
      have h1 : z - b < (6*r+1)*2 := by omega
      have h2 : b + (z-b) = z := by omega
      simpa only [h2] using h (z-b) h1
    constructor
    · intro hod
      rw [Nat.odd_iff] at hod
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨hzT, hzI⟩ := Finset.mem_inter.mp hz
      have hres := (hread z hzI).mp hzT
      have hl := (hc c z).mp hzI
      omega
    · intro hev
      rw [Nat.even_iff] at hev
      refine ⟨b+(c-1)*2, ?_, ?_⟩
      · ext z
        simp only [Finset.mem_inter, Finset.mem_singleton]
        constructor
        · rintro ⟨hzT, hzI⟩
          have hres := (hread z hzI).mp hzT
          have hl := (hc c z).mp hzI
          omega
        · rintro rfl
          have hi : b+(c-1)*2 ∈ cell r 2 s c := (hc c _).mpr (by omega)
          exact ⟨(hread _ hi).mpr (by omega), hi⟩
      · rw [Nat.even_iff]
        omega

open Formalism.G0

/-- When the look-ahead covers every other complete tile, the source's
    requirement at every start is equivalent to existence of one marked tile. -/
theorem tiles_iff_exists (n : ℕ) (T : Finset ℕ) (r u M : ℕ)
    (hn : 0 < n / ((6*r+1)*u)) (hM : n / ((6*r+1)*u) - 1 ≤ M) :
    CondTiles n T r u M ↔ ∃ b < n / ((6*r+1)*u), Marked T r u b := by
  let N := n / ((6*r+1)*u)
  change (∀ a < N, ∃ j ≤ M, Marked T r u ((a+j)%N)) ↔ ∃ b < N, Marked T r u b
  change 0 < N at hn
  change N-1 ≤ M at hM
  constructor
  · intro h
    obtain ⟨j, _, hj⟩ := h 0 hn
    exact ⟨_, Nat.mod_lt _ hn, hj⟩
  · rintro ⟨b, hb, hm⟩ a ha
    by_cases hab : a ≤ b
    · refine ⟨b-a, by omega, ?_⟩
      have hsum : a + (b-a) = b := by omega
      rwa [hsum, Nat.mod_eq_of_lt hb]
    · refine ⟨N+b-a, by omega, ?_⟩
      have hsum : a + (N+b-a) = b+N := by omega
      rwa [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hb]

variable {R : Ranks}

/-- The shared prime filter of the two sides of BadOK. -/
def eligible (s : Scale) (H : Host R) : Finset ℕ := by
  classical
  exact (Finset.range ⌈s.X'⌉₊).filter (fun p => p.Prime ∧
    (baseOf s 0 0 H).IsResidueClassZero p ∧ s.x ^ (s.eps / 4) ≤ (addOrderOf (hPH H p) : ℝ))

/-- In particular the nonconstructive Frobenius choice is held fixed under this update. -/
theorem eligible_update (s : Scale) (H : Host R) (T : Finset R.A) :
    eligible s { H with TT := T } = eligible s H := rfl

def goodAt (s : Scale) (H : Host R) (p : ℕ) (t : R.A) : Prop :=
  let B := baseOf s 0 0 H
  Arith.Loc.Good B (hPH H p) (Arith.bsH (Arith.Loc.stepP B (hPH H p) p) t)

def badPoints (s : Scale) (H : Host R) (p : ℕ) : Finset R.A := by
  classical
  exact H.TT.filter (fun t => ¬goodAt s H p t)

open Classical in
/-- Sum the retained occupancies of bad representatives. Each retained point
    contributes once, including when several points occupy the same bad orbit. -/
theorem badPoints_by_representative (s : Scale) (H : Host R) (p : ℕ) :
    let B := baseOf s 0 0 H
    let h := hPH H p
    let rep := Arith.bsH (Arith.Loc.stepP B h p)
    (badPoints s H p).card =
      ∑ v ∈ (H.TT.image rep).filter (fun v => ¬ Arith.Loc.Good B h v),
        (H.TT.filter (fun t => rep t = v)).card := by
  classical
  dsimp only
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext t
  constructor
  · intro h
    obtain ⟨ht, hg⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨ht, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ ht, hg⟩⟩
  · intro h
    obtain ⟨ht, hv⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨ht, (Finset.mem_filter.mp hv).2⟩

def mass (s : Scale) (H : Host R) : ℝ :=
  ∑ p ∈ eligible s H, Real.log p / p * ((badPoints s H p).card : ℝ)

theorem weight_pos {s : Scale} {H : Host R} {p : ℕ} (hp : p ∈ eligible s H) :
    0 < Real.log p / p := by
  classical
  have hprime : p.Prime := ((Finset.mem_filter.mp hp).2).1
  have hone : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
  exact div_pos (Real.log_pos hone) (by linarith)

theorem mass_zero_iff (s : Scale) (H : Host R) :
    mass s H = 0 ↔ ∀ p ∈ eligible s H, ∀ t ∈ H.TT, goodAt s H p t := by
  classical
  unfold mass
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun p hp => mul_nonneg (weight_pos hp).le (by positivity))]
  constructor
  · intro h p hp t ht
    have hz := (mul_eq_zero.mp (h p hp)).resolve_left (weight_pos hp).ne'
    have he : badPoints s H p = ∅ := Finset.card_eq_zero.mp (by exact_mod_cast hz)
    by_contra hn
    have : t ∈ badPoints s H p := Finset.mem_filter.mpr ⟨ht, hn⟩
    simp [he] at this
  · intro h p hp
    have he : badPoints s H p = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro t ht
      exact (Finset.mem_filter.mp ht).2 (h p hp t (Finset.mem_filter.mp ht).1))
    simp [he]

/-- For a singleton eligible prime the same positive weight cancels exactly.
    This tests the source's threshold, including its numerical factors. -/
theorem badOK_singleton_iff (s : Scale) (Cb : ℝ) (H : Host R) (p : ℕ)
    (hp : eligible s H = {p}) :
    BadOK s Cb H ↔ ((badPoints s H p).card : ℝ) ≤ 4 * (Cb * s.x ^ (-2 : ℝ)) * s.delta1 * R.n := by
  classical
  have hpos : 0 < Real.log p / p := weight_pos (s := s) (H := H) (by simp [hp])
  change (∑ q ∈ eligible s H, Real.log q / q * ((badPoints s H q).card : ℝ)) ≤
      4 * (Cb * s.x ^ (-2 : ℝ)) * s.delta1 * R.n * (∑ q ∈ eligible s H, Real.log q / q) ↔ _
  rw [hp]
  simp only [Finset.sum_singleton]
  rw [mul_comm (Real.log _ / _), mul_le_mul_iff_left₀ hpos]

theorem badOK_zero_iff (s : Scale) (H : Host R) :
    BadOK s 0 H ↔ ∀ p ∈ eligible s H, ∀ t ∈ H.TT, goodAt s H p t := by
  classical
  change mass s H ≤ 4 * (0 * _) * _ * _ * _ ↔ _
  simp only [zero_mul, mul_zero]
  have hnonneg : 0 ≤ mass s H :=
    Finset.sum_nonneg (fun p hp => mul_nonneg (weight_pos hp).le (by positivity))
  rw [le_iff_eq_or_lt, or_iff_left (not_lt.mpr hnonneg), mass_zero_iff]

#print axioms every_arrangement_good
#print axioms one_tile_iff
#print axioms good_one_tile_iff
#print axioms width_two_marked_iff
#print axioms tiles_iff_exists
#print axioms eligible_update
#print axioms badPoints_by_representative
#print axioms mass_zero_iff
#print axioms badOK_singleton_iff
#print axioms badOK_zero_iff

end OrbitAudit
