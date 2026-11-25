import Mathlib
open Finset
namespace TargetOne
def sqSum {R : Type*} [CommRing R] {d : ℕ} (x : Fin d → R) : R := ∑ i, x i ^ 2
noncomputable def count {R : Type*} [CommRing R] (d : ℕ) (b : R) := Nat.card {x : Fin d → R // sqSum x = b}

private def headTail {R : Type*} [CommRing R] (d : ℕ) (b : R) :
    {x : Fin (d+1) → R // sqSum x = b} ≃
      Σ a : R, {y : Fin d → R // sqSum y = b-a^2} where
  toFun x := ⟨x.1 0, (fun i => x.1 i.succ), by
    have h := x.2
    rw [sqSum, Fin.sum_univ_succ] at h
    dsimp [sqSum]; linear_combination h⟩
  invFun x := ⟨Fin.cons x.1 x.2.1, by
    rw [sqSum, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have h := x.2.2
    dsimp [sqSum] at h
    linear_combination h⟩
  left_inv x := Subtype.ext (Fin.cons_self_tail _)
  right_inv x := by rcases x with ⟨a,y,hy⟩; rfl

theorem count_succ {R : Type*} [CommRing R] [Fintype R] (d : ℕ) (b : R) :
    count (d+1) b = ∑ a : R, count d (b-a^2) := by
  simpa only [count,Nat.card_sigma] using Nat.card_congr (headTail d b)

theorem count_zero {R : Type*} [CommRing R] [DecidableEq R] (b : R) :
    count 0 b = if b=0 then 1 else 0 := by
  classical
  by_cases h : b=0
  · subst b
    haveI : Nonempty {x : Fin 0 → R // sqSum x = 0} := ⟨⟨0,by simp [sqSum]⟩⟩
    simpa [count] using Nat.card_unique (α := {x : Fin 0 → R // sqSum x = 0})
  · haveI : IsEmpty {x : Fin 0 → R // sqSum x = b} := ⟨fun x => h (by simpa [sqSum] using x.2.symm)⟩
    simp [count,h]

private def histogram : ℕ → ZMod 8 → ℕ
  | 0,b => if b=0 then 1 else 0
  | d+1,b => ∑ a : ZMod 8, histogram d (b-a^2)

private theorem hist_correct (d : ℕ) (b : ZMod 8) : count d b = histogram d b := by
  induction d generalizing b with
  | zero => exact count_zero b
  | succ d ih => simp only [count_succ, histogram, ih]

private theorem h0 : ∀ b : ZMod 8, histogram 0 b = (![1,0,0,0,0,0,0,0] : Fin 8 → ℕ) ⟨b.val,b.val_lt⟩ := by
  intro b; fin_cases b <;> decide

private theorem h1 : ∀ b : ZMod 8, histogram 1 b = (![2,4,0,0,2,0,0,0] : Fin 8 → ℕ) ⟨b.val,b.val_lt⟩ := by
  intro b
  change (∑ a : ZMod 8, histogram 0 (b-a^2)) = _
  simp only [h0]
  fin_cases b <;> decide

private theorem h2 : ∀ b : ZMod 8, histogram 2 b = (![8,16,16,0,8,16,0,0] : Fin 8 → ℕ) ⟨b.val,b.val_lt⟩ := by
  intro b
  change (∑ a : ZMod 8, histogram 1 (b-a^2)) = _
  simp only [h1]
  fin_cases b <;> decide

private theorem h3 : ∀ b : ZMod 8, histogram 3 b = (![32,96,96,64,32,96,96,0] : Fin 8 → ℕ) ⟨b.val,b.val_lt⟩ := by
  intro b
  change (∑ a : ZMod 8, histogram 2 (b-a^2)) = _
  simp only [h2]
  fin_cases b <;> decide

private theorem h4 : ∀ b : ZMod 8, histogram 4 b = (![128,512,768,512,384,512,768,512] : Fin 8 → ℕ) ⟨b.val,b.val_lt⟩ := by
  intro b
  change (∑ a : ZMod 8, histogram 3 (b-a^2)) = _
  simp only [h3]
  fin_cases b <;> decide

private theorem h5 : ∀ b : ZMod 8, histogram 5 b = (![3072,2560,5120,5120,3072,3584,5120,5120] : Fin 8 → ℕ) ⟨b.val,b.val_lt⟩ := by
  intro b
  change (∑ a : ZMod 8, histogram 4 (b-a^2)) = _
  simp only [h4]
  fin_cases b <;> decide

private theorem h6 : ∀ b : ZMod 8, histogram 6 b = (![32768,24576,30720,40960,32768,24576,34816,40960] : Fin 8 → ℕ) ⟨b.val,b.val_lt⟩ := by
  intro b
  change (∑ a : ZMod 8, histogram 5 (b-a^2)) = _
  simp only [h5]
  fin_cases b <;> decide


theorem base_eight : count 6 (1:ZMod 8) = 24576 := by
  rw [hist_correct, h6]; decide

abbrev red (k : ℕ) : ZMod (8*2^k) →+* ZMod 8 :=
  ZMod.castHom (dvd_mul_right ..) _

private theorem odd_unit (k m : ℕ) : IsUnit (((1+2*m : ℕ) : ZMod (2^k))) :=
  (ZMod.isUnit_iff_coprime ..).2 ((Nat.coprime_two_right.2 ⟨m, by omega⟩).pow_right k)

private theorem digit_surjective (k : ℕ) :
    Function.Surjective (fun x : ZMod (2^k) => x+2*x^2) := by
  apply Finite.injective_iff_surjective.mp
  intro x y h
  have hu : IsUnit (1 + 2*(x+y)) := by
    have := odd_unit k (x+y).val
    simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val] using this
  apply hu.mul_left_cancel
  linear_combination h

theorem square_unit (k : ℕ) (b : ZMod (8*2^k)) (hb : red k b = 1) :
    ∃ u : (ZMod (8*2^k))ˣ, (u : ZMod (8*2^k))^2 = b := by
  have hval : b.val % 8 = 1 := by
    have eq : ((b.val : ℕ) : ZMod 8)=1 := by
      rw [← ZMod.natCast_zmod_val b] at hb
      simpa using hb
    exact (ZMod.natCast_eq_natCast_iff b.val 1 8).mp eq
  obtain ⟨x,hx⟩ := digit_surjective k ((b.val / 8 : ℕ) : ZMod (2^k))
  have he : x.val + 2*x.val^2 ≡ b.val/8 [MOD 2^k] := by
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    push_cast
    simpa using hx
  have hbig := (he.mul_left' 8).add_left 1
  have hdiv : 1+8*(b.val/8)=b.val := by omega
  rw [hdiv] at hbig
  have hpow : (1+4*x.val)^2=1+8*(x.val+2*x.val^2) := by ring
  rw [← hpow] at hbig
  have hu : IsUnit ((1+4*x.val : ℕ) : ZMod (8*2^k)) := by
    have heq : 8*2^k=2^(k+3) := by ring
    rw [heq, show 1+4*x.val=1+2*(2*x.val) by ring]
    exact odd_unit _ _
  refine ⟨hu.unit, ?_⟩
  have hcast := (ZMod.natCast_eq_natCast_iff ..).2 hbig
  simpa only [Units.val_mk0, IsUnit.unit_spec, Nat.cast_pow, ZMod.natCast_zmod_val] using hcast

theorem scaled_count {R : Type*} [CommRing R] (d : ℕ) (u : Rˣ) :
    count d ((u:R)^2) = count d (1:R) := by
  symm
  let e := Equiv.piCongrRight fun _ : Fin d => u.mulLeft
  apply Nat.card_congr (Equiv.subtypeEquiv e ?_)
  intro x
  have he : sqSum (e x) = (u:R)^2 * sqSum x := by
    change (∑ i, ((u:R)*x i)^2) = _ * (∑ i, x i^2)
    simp [Finset.mul_sum, mul_pow]
  rw [he]
  simpa using (u.isUnit.pow 2).mul_right_inj (b := sqSum x) (c := 1) |>.symm

end TargetOne
