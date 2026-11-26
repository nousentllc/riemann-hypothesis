import Init

/-! Finite certificate in O/(π^5), where a is modulo 8 and b is modulo 4.
The address c + 8h represents a square sum c + 2hπ.  Every square has
even π coefficient. Multiplicities below include all input residues. -/
namespace ValuationLedger

abbrev Hist := List Nat
def addresses := List.range 16
def squareAddress (z : Nat) : Nat :=
  let a := z % 8
  let b := z / 8
  (a*a+2*b*b)%8 + 8*((a*b)%2)

def spectrum (parity : Nat) : Hist := addresses.map fun s =>
  ((List.range 32).filter fun z => z%2 == parity && squareAddress z == s).length

theorem square_types :
    spectrum 0 = [4,0,4,0,4,0,4,0, 0,0,0,0,0,0,0,0] ∧
    spectrum 1 = [0,8,0,0,0,0,0,0, 0,0,0,8,0,0,0,0] := by decide

/-- Subtraction of a square residue in the group of attainable coefficient addresses. -/
def minus (s q : Nat) : Nat := ((s%8+8-q%8)%8) + 8*((s/8+2-q/8)%2)

/-- Add one coordinate. The two spectra above each have a common factor of four.
The input weights 1 and 2 below have been divided by that factor. -/
def step (pivot i : Nat) (prior : Hist) : Hist := addresses.map fun s =>
  let atShift := fun q => prior[minus s q]?.getD 0
  let even := atShift 0 + atShift 2 + atShift 4 + atShift 6
  let odd := 2*(atShift 1 + atShift 11)
  if i < pivot then even else if i == pivot then odd else even+odd

def start : Hist := 1 :: List.replicate 15 0
def paths (pivot : Nat) : Hist := (List.range 6).foldl (fun h i => step pivot i h) start
def row (t : Nat) : List Nat := (List.range 6).map fun i => (paths i)[t]?.getD 0

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Primitive counts after the common factor 4^6 has been removed. -/
theorem target_rows :
    row 4 = [7680,4096,2048,1024,512,0] ∧
    row 2 = [8704,4096,2048,1024,512,0] ∧
    row 1 = [8192,4096,2048,1024,512,512] := by decide

/-- Source scaling π^j in six coordinates and target scaling π^(2j)
change density by 16^(-j). At depth five primitive density is count/8192. -/
def table : List (List Nat) :=
  [[3840,2048,1024,512,256,0], [272,128,64,32,16,0], [16,8,4,2,1,1]]

def times (n : Nat) (xs : List Nat) := xs.map (n * ·)

theorem ledger :
    times 4096 (row 4) = times 8192 table[0]! ∧
    times 4096 (row 2) = times (8192*16) table[1]! ∧
    times 4096 (row 1) = times (8192*256) table[2]! := by
  rw [target_rows.1, target_rows.2.1, target_rows.2.2]
  decide

theorem row_totals : table.map List.sum = [7680,512,32] ∧
    (table.map List.sum).sum * 128 = 257 * 4096 := by decide

end ValuationLedger
#print axioms ValuationLedger.square_types
#print axioms ValuationLedger.target_rows
#print axioms ValuationLedger.ledger
#print axioms ValuationLedger.row_totals
