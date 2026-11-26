import Mathlib

namespace FrobeniusGain

/-- The left child contains the chosen representative of its parent orbit.
A leaf records the number retained below the order cutoff. -/
inductive MaskTree where
  | leaf (count : ℕ)
  | fork (even odd : MaskTree)
deriving Repr

namespace MaskTree

def size : MaskTree → ℕ
  | leaf m => m
  | fork l r => l.size + r.size

def depth : MaskTree → ℕ
  | leaf _ => 0
  | fork l r => max l.depth r.depth + 1

def leafBound (b : ℕ) : MaskTree → Prop
  | leaf m => m ≤ b
  | fork l r => l.leafBound b ∧ r.leafBound b

/-- Per node, the odd child gives anchors precisely when the even child has
two retained targets. Retain charges only above a common occupancy threshold. -/
def splitCharge (m : ℕ) : MaskTree → ℕ
  | leaf _ => 0
  | fork l r =>
    (if m ≤ l.size+r.size ∧ 2 ≤ l.size then r.size else 0) +
      l.splitCharge m + r.splitCharge m

/-- Follow the even child when it has two targets. The dropped odd child
then provides usable anchors. Otherwise at most one uncharged point is lost. -/
def harvest (m : ℕ) : MaskTree → ℕ
  | leaf _ => 0
  | fork l r =>
    if m ≤ l.size+r.size then
      if 2 ≤ l.size then r.size+l.harvest m else r.harvest m
    else 0

theorem harvest_le_charges (t : MaskTree) (m : ℕ) : t.harvest m ≤ t.splitCharge m := by
  induction t with
  | leaf n => rfl
  | fork l r hl hr =>
    by_cases h : m ≤ l.size+r.size
    · by_cases h' : 2 ≤ l.size
      · simp [harvest,splitCharge,h,h']; omega
      · simp [harvest,splitCharge,h,h']; omega
    · simp [harvest,h]

theorem size_le_harvest_add (t : MaskTree) {b m : ℕ} (hb : t.leafBound b) :
    t.size ≤ t.harvest m + max b m + t.depth := by
  induction t with
  | leaf n =>
    change n ≤ b at hb
    simpa [size,harvest,depth] using hb.trans (le_max_left b m)
  | fork l r hl hr =>
    obtain ⟨hbl,hbr⟩ := hb
    have el := hl hbl
    have er := hr hbr
    have dl := le_max_left l.depth r.depth
    have dr := le_max_right l.depth r.depth
    by_cases h : m ≤ l.size+r.size
    · by_cases h' : 2 ≤ l.size
      · simp [size,harvest,depth,h,h']; omega
      · simp [size,harvest,depth,h,h']; omega
    · have hmax := le_max_right b m
      simp [size,harvest,depth,h]
      omega

/-- If no oriented collision is possible above the cutoff, occupancy is
bounded by the leaf capacity plus the number of remaining dyadic levels. -/
theorem no_collision_capacity (t : MaskTree) {b : ℕ} (hb : t.leafBound b)
    (hzero : t.splitCharge 0 = 0) : t.size ≤ b + t.depth := by
  have h0 := harvest_le_charges t 0
  have h := size_le_harvest_add t (m := 0) hb
  rw [hzero] at h0
  simp only [max_eq_left (Nat.zero_le b)] at h
  omega

/-- One incidence for each ordered odd anchor/even target pair across the
split, provided the first target has a second distinct even companion.
The difference to the first target then fixes the generator. -/
def adjacentIncidences : MaskTree → ℕ
  | leaf _ => 0
  | fork l r => (if 2 ≤ l.size then l.size*r.size else 0) +
      l.adjacentIncidences + r.adjacentIncidences

theorem adjacent_incidence_bound (t : MaskTree) {b : ℕ} (hb : t.leafBound b) :
    t.size^2 ≤ 2*t.adjacentIncidences + (b+2*t.depth)*t.size := by
  induction t with
  | leaf n =>
    change n ≤ b at hb
    simpa [size,adjacentIncidences,depth,pow_two] using Nat.mul_le_mul_right n hb
  | fork l r hl hr =>
    obtain ⟨hbl,hbr⟩ := hb
    let d := max l.depth r.depth
    let u := l.size
    let v := r.size
    have boundL := (hl hbl).trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right u (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (le_max_left l.depth r.depth)) b)) _)
    have boundR := (hr hbr).trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right v (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (le_max_right l.depth r.depth)) b)) _)
    have hcross : u*v ≤ (if 2 ≤ u then u*v else 0) + (u+v) := by
      by_cases hh : 2 ≤ u
      · simp [hh]
      · simp [hh]
        have hv : u*v ≤ v := by simpa using Nat.mul_le_mul_right v (by omega : u ≤ 1)
        omega
    change (u+v)^2 ≤ 2*((if 2 ≤ u then u*v else 0)+l.adjacentIncidences+r.adjacentIncidences) +
      (b+2*(d+1))*(u+v)
    calc
      (u+v)^2 = u^2+v^2+2*(u*v) := by ring
      _ ≤ (2*l.adjacentIncidences+(b+2*d)*u) + (2*r.adjacentIncidences+(b+2*d)*v) +
          2*((if 2 ≤ u then u*v else 0)+(u+v)) :=
        Nat.add_le_add (Nat.add_le_add boundL boundR) (Nat.mul_le_mul_left 2 hcross)
      _ = _ := by ring

end MaskTree
end FrobeniusGain

#print axioms FrobeniusGain.MaskTree.harvest_le_charges
#print axioms FrobeniusGain.MaskTree.size_le_harvest_add
#print axioms FrobeniusGain.MaskTree.no_collision_capacity
#print axioms FrobeniusGain.MaskTree.adjacent_incidence_bound
