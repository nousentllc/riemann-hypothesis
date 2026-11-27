import CompanionCells

/-! The two unit residues are detected from the image of an actual integral unit. -/
noncomputable section
namespace RamDilate.UnitClass
open RamField OddCell

def representative {A : Type*} [CommRing A] (b : Bool) : QuadraticAlgebra A 2 0 :=
  if b then 1+QuadraticAlgebra.omega else 1

def bit (u : Oˣ) : Bool := decide ((digit 1 (u:O)).im ≠ 0)

theorem bit_false (u : Oˣ) : bit u = false ↔ (digit 1 (u:O)).im = 0 := by
  simp [bit]

theorem bit_true (u : Oˣ) : bit u = true ↔ (digit 1 (u:O)).im = 1 := by
  simp only [bit,decide_eq_true_eq]
  exact (by decide : ∀ a : ZMod 2, a ≠ 0 ↔ a=1) _

private theorem map_pi (r : ℕ) : digit r (pi:O)=pi := by
  apply QuadraticAlgebra.ext <;> first | exact map_zero _ | exact map_one _

theorem map_representative (r : ℕ) (b : Bool) :
    digit r (representative b)=representative b := by
  cases b <;> simp [representative,show (QuadraticAlgebra.omega:O)=pi by rfl,map_pi]

theorem re_one (u : Oˣ) : (digit 1 (u:O)).re = 1 := by
  let v := Units.map (digit 1).toMonoidHom u
  have h := congrArg QuadraticAlgebra.re v.val_inv
  rw [QuadraticAlgebra.re_mul] at h
  change (v:S 1).re * (↑v⁻¹:S 1).re + 2*(v:S 1).im * (↑v⁻¹:S 1).im = 1 at h
  simp only [show (2:ZMod (2^1))=0 by decide,zero_mul,add_zero] at h
  have hn : (v:S 1).re ≠ 0 := by
    intro hz
    rw [hz,zero_mul] at h
    exact (by decide : (0:ZMod 2) ≠ 1) h
  exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a=1) _ hn

theorem digit_class (u : Oˣ) : digit 1 (u:O)=representative (bit u) := by
  apply QuadraticAlgebra.ext
  · rw [re_one]
    cases bit u <;> rfl
  · cases h : bit u with
    | false => exact (bit_false u).mp h
    | true => exact (bit_true u).mp h

/-- Every unit is its class representative plus a multiple of the rational element 2. -/
theorem decomposition (u : Oˣ) : ∃ w : O, (u:O)=representative (bit u)+2*w := by
  let a : O := representative (bit u)
  have h : inc (u:O) ∈ cylinder 1 (digit 1 a) :=
    ⟨(u:O), (digit_class u).trans (map_representative 1 (bit u)).symm,rfl⟩
  rw [← StableOdd.even_cell] at h
  obtain ⟨z,⟨w,hw⟩,hz⟩ := h
  have e : z=(u:O) := inc_injective hz
  change z-a=(pi:O)^(2*1)*w at hw
  rw [e,show (2*1:ℕ)=2 by decide,pi_sq] at hw
  refine ⟨w,?_⟩
  change (u:O)=a+2*w
  linear_combination hw

theorem bit_one : bit (1:Oˣ)=false := by
  apply (bit_false _).mpr
  rw [Units.val_one,map_one,QuadraticAlgebra.im_one]

/-- A specified unit of the second residue class. -/
def twist : Oˣ := (Companion.twist_isUnit (A:=ℤ_[2])).unit

theorem twist_value : (twist:O)=1+pi := IsUnit.unit_spec _

theorem bit_twist : bit twist=true := by
  apply (bit_true _).mpr
  rw [twist_value,map_add,map_one,map_pi]
  rfl

end RamDilate.UnitClass
#print axioms RamDilate.UnitClass.digit_class
#print axioms RamDilate.UnitClass.decomposition
