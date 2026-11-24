import Mathlib

open MeasureTheory Filter Topology

namespace UrielCheck

/-- Conditional reconstruction of the finite-place selection in TPGTail, lines 125–140. -/
theorem finite_places_tail {G V : Type*} [MeasurableSpace G] [Countable V]
    (m : Measure G) (mfin : m Set.univ ≠ ⊤) (P : V → Set G)
    (bad : Finset V → Set G)
    (hbad : ∀ S g, g ∈ bad S ↔ (∀ v ∈ S, g ∈ P v) ∧ ¬ ∀ v, g ∈ P v)
    (hmeas : ∀ S, MeasurableSet (bad S)) (ε : ENNReal) (hε : 0 < ε)
    (S₀ : Finset V) : ∃ S, S₀ ⊆ S ∧ m (bad S) < ε := by
  classical
  have anti : Antitone bad := by
    intro S T hST g hg
    obtain ⟨hall, hn⟩ := (hbad T g).1 hg
    exact (hbad S g).2 ⟨fun v hv => hall v (hST hv), hn⟩
  have emp : ⋂ S, bad S = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro g hg
    have every := Set.mem_iInter.1 hg
    exact ((hbad ∅ g).1 (every ∅)).2 fun v =>
      ((hbad {v} g).1 (every {v})).1 v (Finset.mem_singleton_self v)
  have ten := tendsto_measure_iInter_atTop (μ := m)
    (fun S => (hmeas S).nullMeasurableSet) anti
    ⟨∅, ne_top_of_le_ne_top mfin (measure_mono (Set.subset_univ _))⟩
  rw [emp, measure_empty] at ten
  obtain ⟨S, hlt, hS⟩ := ((ten.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop S₀)).exists
  exact ⟨S, hS, hlt⟩

#print axioms UrielCheck.finite_places_tail
end UrielCheck
