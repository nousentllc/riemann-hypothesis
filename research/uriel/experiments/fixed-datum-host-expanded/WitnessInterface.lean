import Mathlib
noncomputable section
namespace Formalism.FrobeniusOrbits
def HostHyp (q d : ℕ) : Prop :=
  q.Prime ∧ d.Prime ∧ q % 8 = 3 ∧ d % 16 = 7 ∧ jacobiSym (-(d : ℤ)) q = 1

abbrev HGrp (e : ℕ) : Type :=
  (ZMod (2 ^ (e + 2)))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ)

abbrev G0 : Type := ℤˣ × ℤˣ

abbrev GG (e : ℕ) : Type := G0 × HGrp e

def hcl (e : ℕ) (u : (ZMod (2 ^ (e + 2)))ˣ) : HGrp e := QuotientGroup.mk u

def sg (e : ℕ) : GG e := ((-1, 1), 1)

def c0 : G0 := (-1, -1)

end Formalism.FrobeniusOrbits
end
noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

def Idx (n : ℕ) : Type := Fin n

instance (n : ℕ) : Fintype (Idx n) := inferInstanceAs (Fintype (Fin n))
instance (n : ℕ) : DecidableEq (Idx n) := inferInstanceAs (DecidableEq (Fin n))

structure Frame where
  e : ℕ

  ord : ℕ
  grp : AddCommGroup (Idx ord)
  h0 : letI := grp; Idx ord →+ Additive (HGrp e)
  projection_surjective_field : Function.Surjective h0
  gen0 : Idx ord
  zsmul_generator_eq_zero_of_projection : letI := grp; ∀ k : ℤ, h0 (k • gen0) = 0 → k • gen0 = 0

namespace Frame

variable (φ : Frame)

def A : Type := Idx φ.ord

instance : AddCommGroup φ.A := φ.grp
instance : Fintype φ.A := inferInstanceAs (Fintype (Idx φ.ord))
instance : DecidableEq φ.A := inferInstanceAs (DecidableEq (Idx φ.ord))

def A.val {φ : Frame} (t : φ.A) : ℕ := Fin.val (n := φ.ord) t

theorem A.val_lt {φ : Frame} (t : φ.A) : t.val < φ.ord := by
  exact Fin.is_lt (n := φ.ord) t

theorem A.val_injective (φ : Frame) : Function.Injective (A.val : φ.A → ℕ) := by
  exact fun s t h => Fin.ext h

def A.ofVal {φ : Frame} (u : ℕ) (hu : u < φ.ord) : φ.A := (⟨u, hu⟩ : Fin φ.ord)

@[simp] theorem A.val_ofVal {φ : Frame} (u : ℕ) (hu : u < φ.ord) : (A.ofVal u hu : φ.A).val = u := rfl

theorem card_A : Fintype.card φ.A = φ.ord := by
  exact Fintype.card_fin φ.ord

theorem natCard_A : Nat.card φ.A = φ.ord := by
  rw [Nat.card_eq_fintype_card, card_A]

theorem ord_pos : 0 < φ.ord := by
  exact Fin.pos (n := φ.ord) (0 : φ.A)

def h : φ.A →+ Additive (HGrp φ.e) := φ.h0

theorem h_surj : Function.Surjective φ.h := by
  exact φ.projection_surjective_field

def a0 : φ.A := φ.gen0

def A0 : AddSubgroup φ.A := AddSubgroup.zmultiples φ.a0

theorem zsmul_generator_eq_zero_of_image (k : ℤ) (hk : φ.h (k • φ.a0) = 0) : k • φ.a0 = 0 := by
  exact φ.zsmul_generator_eq_zero_of_projection k hk

def n0 : ℕ := addOrderOf φ.a0

def o : ℕ := φ.ord / φ.n0

def dig (s : ℕ) : φ.A := s • φ.a0

theorem dig_def (s : ℕ) : φ.dig s = s • φ.a0 := rfl

def ofNat (u : ℕ) : φ.A := A.ofVal (u % φ.ord) (Nat.mod_lt _ φ.ord_pos)

theorem val_ofNat (u : ℕ) : (φ.ofNat u).val = u % φ.ord := rfl

theorem val_ofNat_of_lt {u : ℕ} (hu : u < φ.ord) : (φ.ofNat u).val = u := by
  rw [φ.val_ofNat u, Nat.mod_eq_of_lt hu]

@[simp] theorem ofNat_val (t : φ.A) : φ.ofNat t.val = t := by
  apply A.val_injective φ
  rw [φ.val_ofNat, Nat.mod_eq_of_lt (A.val_lt t)]

abbrev MA : Type := Multiplicative φ.A

abbrev GG : Type := G0 × φ.MA

def hH : φ.MA →* HGrp φ.e where
  toFun a := (φ.h a.toAdd).toMul
  map_one' := by simp
  map_mul' a b := by simp

def iota (t : φ.A) : φ.MA := Multiplicative.ofAdd t

def iotaInv (a : φ.MA) : φ.A := a.toAdd

def sg : φ.GG := ((-1, 1), 1)

def cc : φ.GG := (c0, 1)

def iod : φ.GG := ((1, -1), 1)

def chD : φ.GG →* ℤˣ := (MonoidHom.snd ℤˣ ℤˣ).comp (MonoidHom.fst G0 φ.MA)

def chQ : φ.GG →* ℤˣ := (MonoidHom.fst ℤˣ ℤˣ).comp (MonoidHom.fst G0 φ.MA)

def chC : φ.GG →* ℂˣ := (Units.map (Int.castRingHom ℂ).toMonoidHom).comp φ.chD

def Psi : Subgroup φ.GG := φ.chD.ker

theorem mem_Psi_iff {φ : Frame} (g : φ.GG) : g ∈ φ.Psi ↔ g.1.2 = 1 := by
  rw [Frame.Psi, MonoidHom.mem_ker]
  rfl

def placeOf {φ : Frame} (g : φ.GG) : φ.GG := if g.1.2 = 1 then g else φ.cc * g

def tau1 (t : φ.A) : φ.GG := ((1, 1), φ.iota t)

def tau2 (t : φ.A) : φ.GG := ((-1, 1), φ.iota t)

def TwoGroup : Prop := ∃ j : ℕ, φ.ord = 2 ^ j

theorem iota_add (s t : φ.A) : φ.iota (s + t) = φ.iota s * φ.iota t := rfl

theorem iota_zero : φ.iota 0 = 1 := rfl

@[simp] theorem iotaInv_iota (t : φ.A) : φ.iotaInv (φ.iota t) = t := rfl

@[simp] theorem iota_iotaInv (a : φ.MA) : φ.iota (φ.iotaInv a) = a := rfl

theorem iota_bijective : Function.Bijective φ.iota := by
  exact Multiplicative.ofAdd.bijective

theorem natCard_GG : Nat.card φ.GG = 4 * φ.ord := by
  show Nat.card (G0 × φ.MA) = _
  rw [Nat.card_prod]
  have h0 : Nat.card G0 = 4 := by
    show Nat.card (ℤˣ × ℤˣ) = 4
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_units_int]
  have h2 : Nat.card φ.MA = φ.ord := φ.natCard_A
  rw [h0, h2]

end Frame

end Formalism.HC

end

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

structure HostRaw (φ : Frame) where
  q : ℕ
  d : ℕ

  QS : ℕ
  hyp : HostHyp q d
  two_le_e : 2 ≤ φ.e
  QS_pos : 0 < QS
  tower_dvd : 2 ^ (φ.e + 2) ∣ QS
  QS_coprime : Nat.Coprime QS (q * d)
  QS_split : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ QS → jacobiSym (-(d : ℤ)) l = 1
  E : Type
  [instField : Field E]
  [instNF : NumberField E]
  galois : IsGalois ℚ E
  gal : (E ≃ₐ[ℚ] E) ≃* φ.GG

  sqd : E
  sqd_sq : sqd ^ 2 = -(d : E)
  gal_sqd : ∀ σ : E ≃ₐ[ℚ] E, σ sqd = ((((gal σ).1.2 : ℤˣ) : ℤ) : E) * sqd

  cycEmb : E →ₐ[ℚ] CyclotomicField (QS * q * d) ℚ
  cycZeta : CyclotomicField (QS * q * d) ℚ
  cycZeta_prim : IsPrimitiveRoot cycZeta (QS * q * d)

  art : (ZMod (QS * q * d))ˣ →* φ.GG
  art_spec : ∀ (u : (ZMod (QS * q * d))ˣ)
    (τ : CyclotomicField (QS * q * d) ℚ ≃ₐ[ℚ] CyclotomicField (QS * q * d) ℚ),
    τ cycZeta = cycZeta ^ (u : ZMod (QS * q * d)).val → ∀ x : E, cycEmb (gal.symm (art u) x) = τ (cycEmb x)
  art_neg_one : art (-1) = φ.cc
  art_h : ∀ (u : (ZMod (QS * q * d))ˣ) (v : (ZMod (2 ^ (φ.e + 2)))ˣ),
    (v : ZMod (2 ^ (φ.e + 2))) = (((u : ZMod (QS * q * d)).val : ℕ) : ZMod (2 ^ (φ.e + 2))) →
    φ.hH (art u).2 = hcl φ.e v
  art_d : ∀ u : (ZMod (QS * q * d))ˣ, (u : ZMod (QS * q * d)).val ≡ 1 [MOD QS * q] → art u = 1 ∨ art u = φ.iod
  art_q : ∀ u : (ZMod (QS * q * d))ˣ, (u : ZMod (QS * q * d)).val ≡ 1 [MOD QS * d] → art u ^ 2 = 1

attribute [instance] HostRaw.instField HostRaw.instNF

namespace HostRaw

variable {φ : Frame} (H : HostRaw φ)

abbrev condN : ℕ := H.QS * H.q * H.d

def small : Finset ℕ := H.QS.primeFactors

abbrev F : Subfield H.E := maximalRealSubfield H.E

def K : IntermediateField ℚ H.E := ℚ⟮H.sqd⟯

abbrev galE (σ : H.E ≃ₐ[ℚ] H.E) : φ.GG := H.gal σ

def conj : H.E ≃ₐ[ℚ] H.E := H.gal.symm φ.cc

def cmType : Set (H.E →+* ℂ) := {ψ | ψ H.sqd = Complex.I * (Real.sqrt H.d : ℂ)}

def psAt (p : ℕ) : ℤ :=
  if h : Nat.Coprime p H.condN then (((H.art (ZMod.unitOfCoprime p h)).1.1 : ℤˣ) : ℤ) else 0

def rd : ℝ := |(discr H.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ H.E : ℝ))

def etaF (𝔭 : Ideal (𝓞 H.F)) : ℤ := if (primesOver 𝔭 (𝓞 H.E)).ncard = 2 then 1 else -1

def MuPM : Prop := ∀ x : H.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → x = 1 ∨ x = -1

def CoprimeFifteen : Prop := Nat.Coprime H.QS 15

def Exact : Prop := ∀ l : ℕ, l.Prime → l ∣ H.QS →
  ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.condN / l] ∧ H.art u ≠ 1

def PsQ : Prop := ∀ u : (ZMod H.condN)ˣ,
  (((H.art u).1.1 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.q

end HostRaw

structure HostDer {φ : Frame} (H : HostRaw φ) : Prop where
  art_surj : Function.Surjective H.art
  cm : IsCMField H.E
  conj_iff : ∀ (ψ : H.E →+* ℂ) (σ : H.E ≃ₐ[ℚ] H.E), (∀ x, ψ (σ x) = starRingEnd ℂ (ψ x)) ↔ H.gal σ = φ.cc
  finrank_E : Module.finrank ℚ H.E = 4 * φ.ord
  finrank_F : Module.finrank ℚ H.F = 2 * φ.ord
  mem_F : ∀ x : H.E, x ∈ H.F ↔ H.conj x = x

  cmType : (∀ ψ : H.E →+* ℂ, ψ ∈ H.cmType ↔ (starRingEnd ℂ).comp ψ ∉ H.cmType) ∧ H.cmType.ncard = 2 * φ.ord ∧
    ∀ ψ ∈ H.cmType, ∀ σ : H.E ≃ₐ[ℚ] H.E, ψ.comp (σ : H.E →+* H.E) ∈ H.cmType ↔ H.gal σ ∈ φ.Psi

  ps_root : ∃ a : H.E, a ≠ 0 ∧ ∀ σ : H.E ≃ₐ[ℚ] H.E, σ a = ((((H.gal σ).1.1 : ℤˣ) : ℤ) : H.E) * a
  art_ch : ∀ u : (ZMod H.condN)ˣ, (((H.art u).1.2 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d

  ps_d : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ H.d [MOD H.QS * H.q] → (H.art u).1.1 = -1

  frob : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
      (∃ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ P) ∧
      (∀ (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ), (u : ZMod H.condN) = (p : ZMod H.condN) →
        (IsArithFrobAt ℤ σ P ↔ H.gal σ = H.art u)) ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ P →
        (((H.gal σ).1.1 : ℤˣ) : ℤ) = H.psAt p ∧ (((H.gal σ).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) p ∧
        ∃ v : (ZMod (2 ^ (φ.e + 2)))ˣ, (v : ZMod (2 ^ (φ.e + 2))) = (p : ZMod _) ∧ φ.hH (H.gal σ).2 = hcl φ.e v) ∧
      ∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ σ = 1

  frob_any : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
    IsArithFrobAt ℤ σ P ↔
      ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u

  inertia : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
    (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔
      ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u

  decomp : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
    σ ∈ MulAction.stabilizer _ P ↔
      ∃ (u : (ZMod H.condN)ˣ) (k : ℕ), (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u

  inertia_d : ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(H.d : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
    (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ (H.gal σ = 1 ∨ H.gal σ = φ.iod)

  decomp_typeI : ∀ (l : ℕ), l.Prime → l ∣ H.QS * H.q →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
      σ ∈ MulAction.stabilizer _ P → H.gal σ ∈ φ.Psi

  decompConj : ∀ (l : ℕ), l.Prime → l ∣ H.condN →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], H.conj ∉ MulAction.stabilizer _ P

  unramEF : ∀ (P : Ideal (𝓞 H.E)), P.IsPrime → P ≠ ⊥ → ¬ ∀ x : 𝓞 H.E, H.conj • x - x ∈ P

  splitK : ∀ p : ℕ, p.Prime →
    ((primesOver (span {(p : ℤ)}) (𝓞 H.K)).ncard = 2 ↔ (p = 2 ∨ (p ≠ 2 ∧ jacobiSym (-(H.d : ℤ)) p = 1)))

  ordinary : ∀ (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
    (∀ σ τ : H.E ≃ₐ[ℚ] H.E, τ ∈ MulAction.stabilizer _ P → (H.gal (σ * τ) ∈ φ.Psi ↔ H.gal σ ∈ φ.Psi)) ↔
      (primesOver (span {(p : ℤ)}) (𝓞 H.K)).ncard = 2

  eta : (∀ 𝔭 : Ideal (𝓞 H.F), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
      (primesOver 𝔭 (𝓞 H.E)).ncard = 2 ∨ ((primesOver 𝔭 (𝓞 H.E)).ncard = 1 ∧ 𝔭.inertiaDegIn (𝓞 H.E) = 2)) ∧
    (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
      ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P →
        (H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = -1 ↔ φ.cc ∈ Subgroup.zpowers (H.gal σ))) ∧
    (∀ (p : ℕ) [Fact p.Prime], p ∣ H.condN →
      ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
        H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = 1)

  diffSupport : ∀ P : Ideal (𝓞 H.E), P.IsPrime → P ∣ differentIdeal (𝓞 H.K) (𝓞 H.E) →
    ((H.QS * H.q : ℕ) : 𝓞 H.E) ∈ P

  principal : ∃ 𝔟 : Ideal (𝓞 H.E), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) ∧ 𝔟 ⊔ H.conj • 𝔟 = ⊤ ∧
    ∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ φ.Psi → σ • 𝔟 = 𝔟

  unimodular : ∀ 𝔟 : Ideal (𝓞 H.E), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) → ∀ x : H.E,
    x ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹) ↔
      ∀ y ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹),
        Algebra.trace H.K H.E (x * H.conj y) ∈ (algebraMap (𝓞 H.K) H.K).range
  discr_sq : discr H.E = discr H.F ^ 2

  discr_primes : (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr H.E → p ∣ H.condN) ∧ (2 : ℤ) ∣ discr H.E ∧ (H.d : ℤ) ∣ discr H.E
  rd_ge : (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) * Real.sqrt H.d ≤ H.rd
  rd_le : H.rd ≤ (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d)
  rd_sq_ge : (4 * φ.ord : ℝ) ≤ H.rd ^ 2

  norm_mu : ∀ x : H.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → Algebra.norm H.K x = 1

def DerOfRaw : Prop := ∀ (φ : Frame) (H : HostRaw φ), HostDer H

structure HostAx (φ : Frame) extends HostRaw φ where
  der : HostDer toHostRaw


end Formalism.HC
end
