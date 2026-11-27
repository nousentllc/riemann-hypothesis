import FiniteCounts
import Mathlib.Algebra.QuadraticAlgebra.Basic

namespace RamBase
open Finset
abbrev R := QuadraticAlgebra (ZMod 32) 2 0
abbrev Pair := Fin 32 × Fin 32
def equiv : R ≃ Pair := QuadraticAlgebra.equivProd 2 0
noncomputable local instance : Fintype R := Fintype.ofEquiv Pair equiv.symm

def encode (z : R) : ℕ := z.re.val * 32 + z.im.val
def decode (i : ℕ) : R := ⟨(i / 32 : ℕ), (i : ℕ)⟩

theorem decode_encode (z : R) : decode (encode z) = z := by
  obtain ⟨a,b⟩ := z
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have hd : (a.val * 32 + b.val) / 32 = a.val := by omega
  have hm : (a.val * 32 + b.val) % 32 = b.val := by omega
  ext
  · simp [decode,encode,hd]
  · apply ZMod.val_injective
    change ((↑(a.val * 32 + b.val) : ZMod 32)).val = b.val
    rw [ZMod.val_natCast,hm]

theorem encode_lt (z : R) : encode z < 1024 := by
  have := ZMod.val_lt z.re
  have := ZMod.val_lt z.im
  unfold encode
  omega

def addUp (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => addUp f n + f n

theorem addUp_eq (n : ℕ) (f : ℕ → ℕ) : addUp f n = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp [addUp]
  | succ n ih => rw [addUp, Fin.sum_univ_castSucc, ih]; rfl

/-- Integer offset used to subtract one square in the two cyclic coordinates.
The added multiple of 32 dominates either square coefficient for 0 ≤ a,b < 32. -/
def back (t a b : ℕ) : ℕ :=
  ((t/32 + 4096 - (a*a+2*b*b)) % 32) * 32 + ((t%32 + 4096 - 2*a*b) % 32)

theorem back_eq (z : R) (a b : Fin 32) :
    back (encode z) a b = encode (z - (⟨a,b⟩ : R)^2) := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := ZMod.val_lt z.im
  have hd : encode z / 32 = z.re.val := by unfold encode; omega
  have hm : encode z % 32 = z.im.val := by unfold encode; omega
  have hA : (a:ℕ)*a+2*(b:ℕ)*b ≤ z.re.val + 4096 := by
    have h₁ := Nat.mul_le_mul (show (a:ℕ) ≤ 31 by omega) (show (a:ℕ) ≤ 31 by omega)
    have h₂ := Nat.mul_le_mul (show (b:ℕ) ≤ 31 by omega) (show (b:ℕ) ≤ 31 by omega)
    rw [Nat.mul_assoc 2]
    omega
  have hB : 2*(a:ℕ)*b ≤ z.im.val + 4096 := by
    have := Nat.mul_le_mul (show 2*(a:ℕ) ≤ 62 by omega) (show (b:ℕ) ≤ 31 by omega)
    omega
  have va : ((a.val : ℕ) : ZMod 32) = (show ZMod 32 from a) := by exact ZMod.natCast_zmod_val (n:=32) a
  have vb : ((b.val : ℕ) : ZMod 32) = (show ZMod 32 from b) := by exact ZMod.natCast_zmod_val (n:=32) b
  rw [back,hd,hm,← ZMod.val_natCast 32, ← ZMod.val_natCast 32]
  simp only [Nat.cast_sub hA,Nat.cast_sub hB,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
    ZMod.natCast_zmod_val,va,vb,encode,pow_two,QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub,
    QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]
  have hh : (4096 : ZMod 32) = 0 := by decide
  simp only [hh,add_zero]
  let x : ZMod 32 := a
  let y : ZMod 32 := b
  have him : 2*x*y = x*y + y*x + 0*y*y := by ring
  change _ * 32 + (z.im - 2*x*y).val = _ * 32 + (z.im - (x*y+y*x+0*y*y)).val
  rw [him]

def step (f : ℕ → ℕ) (t : ℕ) : ℕ :=
  addUp (fun a => addUp (fun b => f (back t a b)) 32) 32

theorem count_step (d : ℕ) (f : ℕ → ℕ)
    (h : ∀ z : R, TargetOne.count d z = f (encode z)) (z : R) :
    TargetOne.count (d+1) z = step f (encode z) := by
  rw [TargetOne.count_succ, ← equiv.symm.sum_comp (fun w : R => TargetOne.count d (z-w^2)),
    Fintype.sum_prod_type,step,addUp_eq]
  apply Finset.sum_congr rfl
  intro a _
  rw [addUp_eq]
  apply Finset.sum_congr rfl
  intro b _
  rw [back_eq, h]
  rfl

/-- Unit-square multiplication transports the entire fiber, with its multiplicity. -/
theorem orbit_count (d : ℕ) (z : R) (u : Rˣ) :
    TargetOne.count d ((u:R)^2*z) = TargetOne.count d z := by
  symm
  let e := Equiv.piCongrRight fun _ : Fin d => u.mulLeft
  apply Nat.card_congr (Equiv.subtypeEquiv e ?_)
  intro x
  have he : TargetOne.sqSum (e x) = (u:R)^2 * TargetOne.sqSum x := by
    change (∑ i, ((u:R)*x i)^2) = _ * (∑ i, x i^2)
    simp [Finset.mul_sum, mul_pow]
  rw [he]
  exact ((u.isUnit.pow 2).mul_right_inj).symm

def checks (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n+1 => checks f n && f n

theorem select {f : ℕ → Bool} {n : ℕ} (h : checks f n = true) (j : ℕ) (hj : j<n) :
    f j = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    by_cases he : j = n
    · simpa [he] using hb
    · exact ih ha (by omega)
end RamBase
