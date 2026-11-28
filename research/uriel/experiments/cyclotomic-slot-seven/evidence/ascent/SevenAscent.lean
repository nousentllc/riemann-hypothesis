import SevenInertia
import SevenRamification
import SevenBase

open NumberField GroundTheory.Global IsDedekindDomain Ideal
open Seven.ClassStep Seven.Inertia Seven.Cover

namespace Seven.Ascent
noncomputable section

/-- One possible finite ramification place. The explicit ramification-index guard
is the only local bound read by the descent, and is computed in the cyclotomic use. -/
def OnePlace (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : Prop :=
  ∃ v : HeightOneSpectrum (𝓞 F),
    (∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver v.asIdeal], P.ramificationIdx (𝓞 F) ≤ p) ∧
    (∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → Algebra.IsUnramifiedIn (𝓞 E) w.asIdeal)

/-- A proof on arbitrary number fields and a variable prime, before selecting seven or any
cyclotomic field. The elementary cover is normal over F by semilinear transport. -/
theorem onePlaceAscent {p : ℕ} [Fact p.Prime] (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F] [IsTotallyComplex E]
    (degree : Module.finrank F E = p) (loc : OnePlace p F E)
    (base : ¬ p ∣ Nat.card (ClassGroup (𝓞 F))) : ¬ p ∣ Nat.card (ClassGroup (𝓞 E)) := by
  intro bad
  obtain ⟨v, ram, away⟩ := loc
  let Ω := AlgebraicClosure E
  let H := Seven.Cover.H E Ω
  let : NumberField H := NumberField.of_module_finite E H
  let : IsGalois F H := _root_.Ascent.Direct.hilbert_galois F E Ω
  let U := Elementary p E Ω
  let : NumberField U := NumberField.of_module_finite E U
  let : IsGalois F U := elementary_galois_downstairs p E Ω F
  let : IsAbelianGalois E U := elementary_abelian p E Ω
  obtain ⟨hp, big⟩ := cover_group F E U degree (elementary_pgroup p E Ω)
    (elementary_degree_pos p E Ω bad)
  obtain ⟨M, hM, hd, hu⟩ := descend F E U v ram away (elementary_unramified p E Ω) hp big
  let _ := hM
  exact base (hd ▸ unramified_degree_dvd F M hu)

/-- An index bound is automatic in a Galois tower. No explicit conductor, total
ramification hypothesis, principal ramified ideal or assumption on the class-group norm
is needed. A designated place outside which the extension is unramified suffices. -/
theorem singlePlaceAscent {p : ℕ} [Fact p.Prime] (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    (degree : Module.finrank F E = p) (v : HeightOneSpectrum (𝓞 F))
    (away : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → Algebra.IsUnramifiedIn (𝓞 E) w.asIdeal)
    (base : ¬ p ∣ Nat.card (ClassGroup (𝓞 F))) : ¬ p ∣ Nat.card (ClassGroup (𝓞 E)) := by
  let _ := NumberField.isTotallyComplex_of_algebra F E
  apply onePlaceAscent F E degree ⟨v, ?_, away⟩ base
  intro P hp hv
  have := v.isMaximal
  have : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  rw [← ramificationIdxIn_eq_ramificationIdx v.asIdeal P Gal(E/F),
      ← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(E/F)) v.asIdeal P,
      ← degree, ← IsGalois.card_aut_eq_finrank]
  exact Subgroup.card_le_card_group _

open Seven.NextLayer Seven.CyclotomicTransport

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem onePlaceSeven (k : ℕ) : OnePlace 7 (Lower k) (Upper k) := by
  classical
  let _ := step_galois k
  obtain ⟨p,hsing⟩ := Set.ncard_eq_one.mp (unique_over_seven k)
  have hm : p ∈ (overPrime 7).primesOver (𝓞 (Lower k)) := hsing ▸ Set.mem_singleton _
  obtain ⟨hp,hov⟩ := hm
  let v : HeightOneSpectrum (𝓞 (Lower k)) :=
    ⟨p,hp, Ideal.ne_bot_of_liesOver_of_ne_bot (show overPrime 7 ≠ ⊥ by norm_num [overPrime]) p⟩
  refine ⟨v, ?_, ?_⟩
  · intro P _ hOver
    rw [← ramificationIdxIn_eq_ramificationIdx v.asIdeal P Gal(Upper k / Lower k)]
    exact (ramification_seven k p).2.1.le
  · intro w hn
    apply (unramified_iff k w.asIdeal w.ne_bot).2
    intro hOver
    have hmem : w.asIdeal ∈ (overPrime 7).primesOver (𝓞 (Lower k)) := ⟨w.isPrime,hOver⟩
    have heq : w.asIdeal = p := by simpa only [hsing,Set.mem_singleton_iff] using hmem
    exact hn (by ext; rw [show v.asIdeal = p from rfl, heq])

theorem ascend (k : ℕ) (base : ¬7 ∣ Nat.card (ClassGroup (𝓞 (Lower k)))) :
    ¬7 ∣ Nat.card (ClassGroup (𝓞 (Upper k))) := by
  let _ := step_galois k
  let _ : IsTotallyComplex (Lower k) := totally_complex k
  let _ : IsTotallyComplex (Upper k) := totally_complex (k+1)
  exact onePlaceAscent (Lower k) (Upper k) (step_degree k) (onePlaceSeven k) base

theorem regularLayer (k : ℕ) : ¬7 ∣ Nat.card (ClassGroup (𝓞 (Lower k))) := by
  induction k with
  | zero =>
    let _ : IsCyclotomicExtension {7} ℚ (Lower 0) := by
      simpa using rational_cyclotomic 1 (by decide)
    exact SlotSevenProbe.seven_not_dvd_class _
  | succ k ih => exact ascend k ih

theorem allCyclotomicLayers (n : ℕ) (hn : 1 ≤ n) :
    ¬7 ∣ Nat.card (ClassGroup (𝓞 (UpperTheory.V.Kum.Fn (CyclotomicField 7 ℚ)
      (AlgebraicClosure (CyclotomicField 7 ℚ)) 7 n))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact regularLayer k

theorem allStandardLayers (n : ℕ) (hn : 1 ≤ n) :
    ¬7 ∣ Nat.card (ClassGroup (𝓞 (CyclotomicField (7^n) ℚ))) := by
  rw [← class_card n hn]
  exact allCyclotomicLayers n hn

#print axioms onePlaceAscent
#print axioms singlePlaceAscent
#print axioms onePlaceSeven
#print axioms ascend
#print axioms regularLayer
#print axioms allCyclotomicLayers
#print axioms allStandardLayers
end
end Seven.Ascent
