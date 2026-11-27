import RamBase
namespace RamPrecision
open RamBase
set_option maxRecDepth 20000

/-- Examine all depth-ten descendants of the depth-five residue of four.
Each of its two depth-six children is a constant row of the certified census. -/
private theorem certify : checks (fun k => decide (
    (decode k).re.val % 8 = 4 → (decode k).im.val % 4 = 0 →
    row6 (repNo k) = (if (decode k).im.val % 8 = 0 then 257 else 255)*2^43)) 1024 = true := by
  decide +kernel

theorem coarse_children (x : R) (ha : x.re.val % 8=4) (hb : x.im.val % 4=0) :
    TargetOne.count 6 x = (if x.im.val % 8=0 then 257 else 255)*2^43 := by
  have h := of_decide_eq_true (select certify (encode x) (encode_lt x))
  simp only [decode_encode] at h
  exact (census_six x).trans (h ha hb)

theorem different_sibling : TargetOne.count 6 (⟨4,4⟩:R) = 255*2^43 := by
  exact coarse_children _ (by decide) (by decide)
end RamPrecision
#print axioms RamPrecision.coarse_children
