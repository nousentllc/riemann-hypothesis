"""Produce two strengthened declarations from the pinned original without modifying the checkout."""
from pathlib import Path


def once(s,a,b):
    if s.count(a)!=1:
        raise ValueError(a)
    return s.replace(a,b,1)


def render(root):
    base=root/"src/Development/AutomorphicArithmetic"
    fld=(base/"CharacterBoxes/FieldChi.lean").read_text()
    for a,b in [
        ("theorem UpperTheory.Top.fieldChi :","theorem MarkedWindows.fieldChiWithCap :"),
        ("1 ≤ c ∧ ∀ e ≥ e0","1 ≤ c ∧ c ≤ Nat.card (Subgroup.zpowers ψ.χ) ∧ ∀ e ≥ e0"),
        ("hc1, -, hord","hc1, hcap, hord"),("ψ.χ)))), hc1,","ψ.χ)))), hc1, hcap,")]:
        fld=once(fld,a,b)
    sup=(base/"ShortNorms/supplyOfAdmOf.lean").read_text()
    for a,b in [
        ("theorem UpperTheory.T3.supplyOfAdmOf :","theorem MarkedWindows.supplyWithSupport (lam : ℝ) :"),
        ("→ ∀ ψ : PChar, VWinAt ψ 401","→ ∀ ψ : PChar, (lam < 2 ∨ lam = 2 ∧ ψ = PChar.one) → VWinAt ψ 401"),
        ("HostExW (3 / 2)", "MarkedWindows.MarkedHost ψ lam"),
        ("intro hSup ψ hV hAdm eps", "intro hSup ψ hlam hV hAdm eps"),
        ("⟨c, e0, hc, hF⟩ := UpperTheory.Top.fieldChi ψ", "⟨c, e0, hc, hcap, hF⟩ := MarkedWindows.fieldChiWithCap ψ"),
        ("UpperTheory.Top.winPairs ψ eps (c : ℝ) heps heps' (by exact_mod_cast hc) hV QH.pairEx","MarkedWindows.winsFor ψ eps lam c heps heps' hc hcap hlam hV QH.pairEx"),
        ("Y q d e}, hwin⟩, ?_⟩","Y q d e}, hwin⟩, ⟨c, hc, hcap, rfl⟩, ?_⟩")]:
        sup=once(sup,a,b)
    return {"CapField.lean":fld+"\n#print axioms MarkedWindows.fieldChiWithCap\n",
            "MarkedSupply.lean":"import UnitCases\nimport CapField\n"+sup+"\n#print axioms MarkedWindows.supplyWithSupport\n"}
