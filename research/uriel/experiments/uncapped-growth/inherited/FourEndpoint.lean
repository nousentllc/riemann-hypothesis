import Existence
import FourContact
import FourTubes
import FourNeighborhood
open TargetOne HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped ENNReal TensorProduct Matrix
noncomputable section
namespace TargetFour
abbrev atFour : H := hermScal K conjG 4
def evenLattice : Set W := {X | ∀ a i j,
  (Algebra.TensorProduct.basis K gb).repr (X a i) j ∈ cylinder 1 0}
def primitiveLattice : Set W := lattice \ evenLattice

theorem even_sub : evenLattice ⊆ lattice := by
  intro X h a i j
  obtain ⟨y,_,hy⟩ := h a i j
  rw [←hy]
  exact (ei y).2

theorem even_compact_open : IsCompact evenLattice ∧ IsOpen evenLattice := by
  obtain ⟨i1,i2,i3,i4,-⟩ := locally
  obtain ⟨-, -, -, -, -, -, hH, -⟩ := GlobalTheory.T.tensor_locally_compact_ring ℚ E conjG isCM K
  let f : K ⊗[ℚ] E → Fin 2 → K := fun y k => (Algebra.TensorProduct.basis K gb).repr y k
  let e := (hH 2 gb).homeomorph f
  let P : Set (Fin 2 → K) := Set.pi Set.univ fun _ => cylinder 1 0
  let B := e ⁻¹' P
  have hBc : IsCompact B := (Homeomorph.isCompact_preimage e).2 (isCompact_univ_pi fun _ => compact_cylinder _ _)
  have hBo : IsOpen B := (Homeomorph.isOpen_preimage e).2
    (isOpen_set_pi Set.finite_univ fun _ _ => open_cylinder _ _)
  have he : evenLattice = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => B := by
    ext Y
    simp only [evenLattice,Set.mem_setOf_eq,Set.mem_pi,Set.mem_univ,true_implies,B,P,Set.mem_preimage]
    rfl
  rw [he]
  exact ⟨isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hBc,
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hBo⟩

private theorem four_regular : (4:K) ≠ 0 := by
  have h := (map_ne_zero_iff (algebraMap ℚ K) (RingHom.injective _)).2 (show (4:ℚ) ≠ 0 by decide)
  simpa only [map_ofNat] using h

private theorem even_test (r : ℕ) :
    {x : Idx → K | x ∈ evenBox ∧ Q x ∈ cylinder r 4} = tube r 4 ∩ evenBox := by
  ext x
  constructor
  · rintro ⟨hx,hq⟩
    refine ⟨⟨fun i => ?_,hq⟩,hx⟩
    obtain ⟨y,_,he⟩ := hx i (Set.mem_univ _)
    rw [← he]; exact (ei y).2
  · rintro ⟨⟨_,hq⟩,hx⟩; exact ⟨hx,hq⟩

theorem total_mass (lam : Measure K) (hlam : IsStdV placeTwo lam)
    (m : H → Measure W) (hm : family lam m) : m atFour lattice=(63/64:ℝ≥0∞) := by
  classical
  obtain ⟨i1,i2,i3,i4,-⟩ := locally
  haveI := hlam.1
  have hU : IsOpen ({0}ᶜ : Set K) := isOpen_compl_singleton
  have hs : (4:K) ∈ ({0}ᶜ : Set K) := four_regular
  have h := local_mass_from_tests conjG isCM 3 J herm_id 2 gb placeTwo
    ((2:K) • (1 : Matrix Idx Idx K)) (trace_coords K) lam hlam m hm 4 (63/64)
    {0}ᶜ hU hs (fun _ hz => hz) locally lattice_clopen.1 lattice_clopen.2
  have hval : (m atFour lattice).toReal=(63/64:ℝ) := by
    apply (show _ → (m atFour lattice).toReal=63/64 from fun hD => by simpa using h hD)
    intro N hN
    obtain ⟨k,hc⟩ := small_four _ (Filter.inter_mem (hU.mem_nhds hs) hN)
    refine ⟨cylinder (k+4) 4,compact_cylinder _ _,hc,?_,?_⟩
    · rw [Measure.real,cyl_mass lam hlam.2,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
      positivity
    · simp only [half_coord]
      change (Measure.pi fun _ : Idx => lam) (tube (k+4) 4) = _
      simpa using total_tube lam hlam.2 (k+4) (by omega)
  have hfin : m atFour lattice ≠ ⊤ := by intro ht; rw [ht,ENNReal.toReal_top] at hval; norm_num at hval
  apply (ENNReal.toReal_eq_toReal_iff' hfin (by finiteness)).mp
  simpa using hval

theorem even_mass (lam : Measure K) (hlam : IsStdV placeTwo lam)
    (m : H → Measure W) (hm : family lam m) : m atFour evenLattice=(3/64:ℝ≥0∞) := by
  classical
  obtain ⟨i1,i2,i3,i4,-⟩ := locally
  haveI := hlam.1
  have hU : IsOpen ({0}ᶜ : Set K) := isOpen_compl_singleton
  have hs : (4:K) ∈ ({0}ᶜ : Set K) := four_regular
  have hP : MeasurableSet evenBox := MeasurableSet.pi Set.countable_univ fun i _ => (open_cylinder 1 0).measurableSet
  have hcoords (X : W) : X ∈ evenLattice ↔ (fun p : Idx =>
      (Algebra.TensorProduct.basis K gb).repr (X 0 p.1) p.2) ∈ evenBox := by
    constructor
    · intro h i _; exact h 0 i.1 i.2
    · intro h a i j; obtain rfl : a=0 := Subsingleton.elim _ _; exact h (i,j) (Set.mem_univ _)
  have h := mass_of_coordinate_set conjG isCM 3 J herm_id 2 gb placeTwo
    ((2:K) • (1 : Matrix Idx Idx K)) (trace_coords K) lam hlam m hm 4 (3/64)
    {0}ᶜ hU hs (fun _ hz => hz) locally evenLattice evenBox hP hcoords even_compact_open.1 even_compact_open.2
  have hval : (m atFour evenLattice).toReal=(3/64:ℝ) := by
    apply (show _ → (m atFour evenLattice).toReal=3/64 from fun hD => by simpa using h hD)
    intro N hN
    obtain ⟨k,hc⟩ := small_four _ (Filter.inter_mem (hU.mem_nhds hs) hN)
    refine ⟨cylinder (k+4) 4,compact_cylinder _ _,hc,?_,?_⟩
    · rw [Measure.real,cyl_mass lam hlam.2,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
      positivity
    · simp only [half_coord,even_test]
      simpa using even_tube lam hlam.2 (k+4) (by omega)
  have hfin : m atFour evenLattice ≠ ⊤ := by intro ht; rw [ht,ENNReal.toReal_top] at hval; norm_num at hval
  apply (ENNReal.toReal_eq_toReal_iff' hfin (by finiteness)).mp
  simpa using hval

theorem primitive_mass (lam : Measure K) (hlam : IsStdV placeTwo lam)
    (m : H → Measure W) (hm : family lam m) : m atFour primitiveLattice=(15/16:ℝ≥0∞) := by
  obtain ⟨i1,i2,i3,i4,-⟩ := locally
  obtain ⟨-, -, -, -, -, -, -, hBorW, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring ℚ E conjG isCM K
  haveI : BorelSpace W := hBorW 1 3
  have he := even_mass lam hlam m hm
  rw [primitiveLattice,measure_diff even_sub even_compact_open.2.measurableSet.nullMeasurableSet
    (by rw [he]; finiteness),total_mass lam hlam m hm,he]
  apply (ENNReal.toReal_eq_toReal_iff' (ne_top_of_le_ne_top (by finiteness : (63/64:ℝ≥0∞)≠⊤) tsub_le_self) (by finiteness)).mp
  rw [ENNReal.toReal_sub_of_le (by gcongr <;> norm_num) (by finiteness)]
  norm_num [ENNReal.toReal_div]

theorem transfer (lam : Measure K) (hlam : IsStdV placeTwo lam)
    (m : H → Measure W) (hm : family lam m) :
    m atFour evenLattice = (1/16:ℝ≥0∞)*m target lattice := by
  rw [even_mass lam hlam m hm,target_one_mass lam hlam m hm]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_div]

theorem realized_split : ∃ lam : Measure K, IsStdV placeTwo lam ∧ ∃ m : H → Measure W,
    family lam m ∧ m atFour lattice=63/64 ∧ m atFour primitiveLattice=15/16 ∧
    m atFour evenLattice=3/64 ∧ m atFour evenLattice=(1/16)*m target lattice := by
  obtain ⟨lam,hlam⟩ := standard_exists
  obtain ⟨m,hm,_⟩ := realized lam hlam
  exact ⟨lam,hlam,m,hm,total_mass lam hlam m hm,primitive_mass lam hlam m hm,
    even_mass lam hlam m hm,transfer lam hlam m hm⟩
end TargetFour
#print axioms TargetFour.realized_split
