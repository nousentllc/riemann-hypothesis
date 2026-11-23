import Mathlib

namespace TenPercent

def selected (width mask : Nat) : List Nat :=
  (List.range width).filter (fun i => mask.testBit i)

/-- Tree swaps have heap indices 0,1,...,6; the input is the canonical leaf rank. -/
def permAt (word : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | d+1, node, i =>
    let h := 2^d
    let side := i/h
    let imageSide := if word.testBit node then 1-side else side
    imageSide*h + permAt word d (2*node+1+side) (i%h)

/-- Seven rows in their first-unflipped-bit order. -/
def menu (word : Nat) : Nat :=
  if !word.testBit 0 then 0x070f else
  if !word.testBit 2 then 0x0331 else
  if !word.testBit 5 then 0x07d1 else
  if !word.testBit 6 then 0x0d71 else
  if !word.testBit 1 then 0x3101 else
  if !word.testBit 3 then 0x5101 else 0xd107

def crudeLedger : Nat → Nat → Int
  | 0, mask => if mask.testBit 0 then -1 else 0
  | d+1, mask =>
    let h := 2^d
    let left := mask % 2^h
    let right := mask / 2^h
    let a := (selected h left).length
    let b := (selected h right).length
    let absent := h - 2*a*b
    crudeLedger d left + crudeLedger d right +
      (b : Int)*(20*(absent : Int) - 2*(h : Int))

def measuredMargin (word : Nat) : Int :=
  let mask := menu word
  let n := (selected 16 mask).length
  let pairs := ((List.range 8).filter (fun i =>
    mask.testBit i && mask.testBit (8+permAt word 3 0 i))).length
  let absent := 16 - 2*(n-pairs)
  let reservoir : Int := if n==7 then -195 else if n==5 then -331 else -362
  crudeLedger 4 mask + (n : Int)*(20*(absent : Int)-32-64) - 65 + reservoir

def rowFloor (word : Nat) : Int :=
  if !word.testBit 0 then 115 else
  if !word.testBit 2 then 67 else
  if !word.testBit 5 then 93 else
  if !word.testBit 6 then 93 else
  if !word.testBit 1 then 39 else
  if !word.testBit 3 then 37 else 77

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem seven_nonreversal_rows :
    ∀ i : Fin 127, 37 ≤ rowFloor i.val ∧ rowFloor i.val ≤ measuredMargin i.val := by
  decide +kernel

theorem last_swap_word_is_reversal :
    ∀ i : Fin 8, permAt 127 3 0 i.val = 7-i.val := by decide +kernel

def reverseThree (i : Nat) : Nat :=
  i/4 + 2*(i/2%2) + 4*(i%2)

def exceptionalLayout : List Nat :=
  let even := ([0,1,3,2,5,4,6,7] : List Nat).map (fun i => 2*reverseThree i)
  even ++ even.reverse.map (fun i => 15-i)

def exactLedger : Nat → List Nat → Nat → Int
  | 0, _, mask => if mask.testBit 0 then -1 else 0
  | d+1, coords, mask =>
    let h := 2^d
    let left := mask % 2^h
    let right := mask / 2^h
    let positions := (selected (2*h) mask).map (fun i => coords[i]!)
    let absent := ((List.range h).filter (fun j =>
      positions.all (fun t => !(positions.contains ((t+2*j+1)%(2*h)))))).length
    exactLedger d ((coords.take h).map (·/2)) left +
      exactLedger d ((coords.drop h).map (·/2)) right +
      ((selected h right).length : Int)*(20*(absent : Int)-2*(h : Int))

theorem exceptional_ledger :
    (selected 16 0xd101).length = 5 ∧
    ((List.range 16).filter (fun i =>
      !(0xd101 : Nat).testBit i && !(0xd101 : Nat).testBit (15-i))).length = 8 ∧
    exactLedger 4 exceptionalLayout 0xd101 = 57 := by
  decide +kernel

/-- Scalar arithmetic after the reservoir and singleton lower bounds are supplied. -/
theorem weighted_margin :
    22*(411/176 : ℚ) + 3/4 + 5*(19/8) = 64 ∧
    (19/8 : ℚ)*(57+5*(20*8-32-64)) +
      (411/176)*(-256-32*6+86) - 65*(3/4) = 14/11 ∧
    (14/11 : ℚ) ≤ (64/27)*37 := by norm_num

/-- Conversion uses an upper bound on this same profile's denominator. -/
theorem fraction_bound (r k : ℝ) (hk : 0 < k) (hcap : k ≤ 64*127)
    (hmargin : (14:ℝ)/11 ≤ 10*r-k) :
    1/10 + 7/447040 ≤ r/k := by
  apply (le_div_iff₀ hk).2
  linarith

#print axioms seven_nonreversal_rows
#print axioms last_swap_word_is_reversal
#print axioms exceptional_ledger
#print axioms weighted_margin
#print axioms fraction_bound

end TenPercent
