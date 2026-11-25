import FourEven

/-! A four-square control at the dyadic place. The generic helpers and residue
maps are the exact ones from our target-four study. No fiber family is assumed.
-/
open Finset TargetOne TargetFour
noncomputable section
namespace FourSquareControl
set_option maxHeartbeats 4000000
set_option maxRecDepth 32000

private theorem mod_eight_control :
    ∀ a b c d : ZMod 8, a^2+b^2+c^2+d^2=0 →
      a.val%2=0 ∧ b.val%2=0 ∧ c.val%2=0 ∧ d.val%2=0 := by decide

private theorem only_even {m t : ℕ} [NeZero m] (hm : 2 ∣ m) (ht : 2 ∣ t)
    (x : Fin 4 → ZMod (4*m)) (hx : sqSum x = (4*t:ℕ)) :
    ∀ j, (x j).val%2=0 := by
  obtain ⟨n,hn⟩ := hm
  have hdiv : 8 ∣ 4*m := ⟨n,by rw [hn]; ring⟩
  let red := ZMod.castHom hdiv (ZMod 8)
  have H : sqSum (fun j => red (x j))=0 := by
    have he := congrArg red hx
    simp only [sqSum,map_sum,map_pow,map_natCast] at he ⊢
    obtain ⟨l,hl⟩ := ht
    rw [hl,show 4*(2*l)=8*l by ring,Nat.cast_mul,Nat.cast_ofNat,show (8:ZMod 8)=0 by decide,zero_mul] at he
    exact he
  simp only [sqSum,Fin.sum_univ_four] at H
  have hh := mod_eight_control _ _ _ _ H
  have hred (a : ZMod (4*m)) : (red a).val%2 = a.val%2 := by
    have e := congrArg red (ZMod.natCast_zmod_val a)
    simp only [map_natCast] at e
    rw [←e, ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 8)]
  simp only [hred] at hh
  intro j; fin_cases j <;> tauto

private theorem equation (m t : ℕ) [NeZero m] (y : Fin 4 → ZMod (m*2)) :
    sqSum (fun i => twice m (y i))=(4*t:ℕ) ↔ sqSum (fun i => reduce m 2 (y i))=(t:ℕ) := by
  let S := ∑ i, (y i).val^2
  have hL : sqSum (fun i => twice m (y i)) = ((4*S : ℕ) : ZMod (4*m)) := by
    simp only [sqSum,twice,S,Nat.cast_mul,Nat.cast_pow,Nat.cast_sum,mul_pow,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; norm_num
  have hR : sqSum (fun i => reduce m 2 (y i))=(S : ZMod m) := by
    simp only [sqSum,S,Nat.cast_sum,Nat.cast_pow]
    apply Finset.sum_congr rfl; intro i _
    have h := congrArg (reduce m 2) (ZMod.natCast_zmod_val (y i))
    simpa only [map_natCast] using congrArg (fun z : ZMod m => z^2) h.symm
  rw [hL,hR]
  have h := Nat.ModEq.mul_left_cancel_iff' (a := S) (b := t) (m := m) (by decide : 4≠0)
  rw [← ZMod.natCast_eq_natCast_iff,← ZMod.natCast_eq_natCast_iff] at h
  simpa only [mul_one,Nat.cast_ofNat,Nat.cast_one] using h

private def halveSolutions (m t : ℕ) [NeZero m] :
    {x : Fin 4 → ZMod (4*m) // sqSum x=(4*t:ℕ) ∧ ∀ j, (x j).val%2=0} ≃
    {y : Fin 4 → ZMod (m*2) // sqSum (fun i => reduce m 2 (y i))=(t:ℕ)} where
  toFun x := ⟨fun i => half m (x.1 i), by
    apply (equation m t _).mp
    have h (i) : twice m (half m (x.1 i))=x.1 i := by
      apply ZMod.val_injective; rw [twice_val,half_val]
      have := x.2.2 i; omega
    simpa only [h] using x.2.1⟩
  invFun y := ⟨fun i => twice m (y.1 i), (equation m t _).mpr y.2,
    fun i => by rw [twice_val]; omega⟩
  left_inv x := by
    apply Subtype.ext; funext i
    apply ZMod.val_injective
    change (twice m (half m (x.1 i))).val=_
    rw [twice_val,half_val]; have := x.2.2 i; omega
  right_inv y := by
    apply Subtype.ext; funext i
    apply ZMod.val_injective
    change (half m (twice m (y.1 i))).val=_
    rw [half_val,twice_val]; omega

private theorem even_scaling (m t : ℕ) [NeZero m] (hm : 2 ∣ m) (ht : 2 ∣ t) :
    count 4 ((4*t:ℕ):ZMod (4*m)) = 16*count 4 (t:ZMod m) := by
  classical
  let small := univ.filter fun z : Fin 4 → ZMod m => sqSum z=(t:ℕ)
  let g := fun (y : Fin 4 → ZMod (m*2)) (i : Fin 4) => reduce m 2 (y i)
  have h := partitions g small
  have he : Nat.card {y : Fin 4 → ZMod (m*2) // sqSum (g y)=(t:ℕ)} =
      Nat.card {y : Fin 4 → ZMod (m*2) // g y ∈ small} := by
    apply Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) ?_)
    intro x; change sqSum (g x)=(t:ℕ) ↔ g x ∈ Finset.filter _ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have lift (z : Fin 4 → ZMod m) : Nat.card {x // g x=z}=16 := by
    let e : {x // g x=z} ≃ ((i : Fin 4) → {a : ZMod (m*2) // reduce m 2 a=z i}) :=
      {toFun := fun x i => ⟨x.1 i,congrFun x.2 i⟩
       invFun := fun x => ⟨fun i => (x i).1,funext fun i => (x i).2⟩
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl}
    rw [Nat.card_congr e,Nat.card_pi]
    simp only [scalar_count,Finset.prod_const,Finset.card_univ,Fintype.card_fin]; decide
  have hs : small.card = count 4 (t:ZMod m) := by simp [small,count,Nat.card_eq_fintype_card,Fintype.card_subtype]
  let e : {x : Fin 4 → ZMod (4*m) // sqSum x=(4*t:ℕ)} ≃
          {x : Fin 4 → ZMod (4*m) // sqSum x=(4*t:ℕ) ∧ ∀j,(x j).val%2=0} :=
    { toFun := fun x => ⟨x.1,x.2,only_even hm ht x.1 x.2⟩
      invFun := fun x => ⟨x.1,x.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [count,Nat.card_congr e,Nat.card_congr (halveSolutions m t),he,h]
  simp only [lift,Finset.sum_const,nsmul_eq_mul,hs,Nat.mul_comm,Nat.cast_id]
private def independent (n t : ℕ) (y : Fin 4 → ZMod n) :
    {x : Fin 4 → ZMod (n*t) // (fun i => reduce n t (x i))=y} ≃
      ((i : Fin 4) → {z : ZMod (n*t) // reduce n t z=y i}) where
  toFun x i := ⟨x.1 i,congrFun x.2 i⟩
  invFun x := ⟨fun i => (x i).1,funext fun i => (x i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem scaled4 {R : Type*} [CommRing R] (u : Rˣ) (a : R) :
    count 4 ((u:R)^2*a) = count 4 a := by
  symm
  let e := Equiv.piCongrRight fun _ : Fin 4 => u.mulLeft
  apply Nat.card_congr (Equiv.subtypeEquiv e ?_)
  intro x
  have he : sqSum (e x)=(u:R)^2*sqSum x := by
    change (∑ i, ((u:R)*x i)^2) = _ * (∑ i, x i^2)
    simp [Finset.mul_sum,mul_pow]
  rw [he]
  exact ((u.isUnit.pow 2).mul_right_inj).symm

private theorem orbit_count4 (k : ℕ) :
    count 4 (4 : ZMod (32*2^k)) = count 4 (4 : ZMod 32)*(2^k)^3 := by
  classical
  let small := univ.filter fun y : Fin 4 → ZMod 32 => sqSum y=4
  let targets := univ.filter fun t : ZMod (32*2^k) => reduce 32 (2^k) t=4
  let r := fun (x : Fin 4 → ZMod (32*2^k)) (i : Fin 4) => reduce 32 (2^k) (x i)
  have hs : small.card=count 4 (4:ZMod 32) := by simp [count,small,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have ht : targets.card=2^k := by
    change (univ.filter (fun t : ZMod (32*2^k) => reduce 32 (2^k) t=4)).card = _
    convert scalar_count 32 (2^k) 4 using 1
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have fine : ∀ t ∈ targets, count 4 t = count 4 (4:ZMod (32*2^k)) := by
    intro t ht
    obtain ⟨u,hu⟩ := factor k t (Finset.mem_filter.mp ht).2
    rw [hu,scaled4]
  have h1 := partitions r small
  have h2 := partitions (@sqSum (ZMod (32*2^k)) _ 4) targets
  have hc (x : Fin 4 → ZMod (32*2^k)) : r x ∈ small ↔ sqSum x ∈ targets := by
    change _ ∈ Finset.filter _ _ ↔ _ ∈ Finset.filter _ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    change (∑ i, (reduce 32 (2^k) (x i))^2)=4 ↔ reduce 32 (2^k) (∑ i,x i^2)=4
    rw [map_sum]; simp only [map_pow]
  have he : Nat.card {x // r x ∈ small}=Nat.card {x : Fin 4 → ZMod (32*2^k) // sqSum x ∈ targets} :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (fun x => hc x))
  have lifts (y : Fin 4 → ZMod 32) : Nat.card {x // r x=y}=(2^k)^4 := by
    rw [Nat.card_congr (independent 32 (2^k) y), Nat.card_pi]
    simp only [scalar_count,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simp_rw [lifts] at h1
  change _ = ∑ s ∈ targets, count 4 s at h2
  rw [Finset.sum_congr rfl fine] at h2
  simp only [sum_const,nsmul_eq_mul,hs,ht] at h1 h2
  apply Nat.eq_of_mul_eq_mul_left (show 0<2^k by positivity)
  calc _ = count 4 (4:ZMod 32)*(2^k)^4 := h2.symm.trans (he.symm.trans h1)
       _ = _ := by ring
private def hist {m : ℕ} [NeZero m] : ℕ → ZMod m → ℕ
  | 0,b => if b=0 then 1 else 0
  | d+1,b => ∑ a : ZMod m, hist d (b-a^2)
private theorem exact_hist {m : ℕ} [NeZero m] (d : ℕ) (b : ZMod m) : count d b = hist d b := by
  induction d generalizing b with
  | zero => exact count_zero b
  | succ d ih => simp only [count_succ,hist,ih]
private theorem row_8_0 (b : ZMod 8) : hist 0 b = (![1,0,0,0,0,0,0,0] : Fin 8 → ℕ) ⟨b.val,b.val_lt⟩ := by
  fin_cases b <;> decide
private theorem row_8_1 (b : ZMod 8) : hist 1 b = (![2,4,0,0,2,0,0,0] : Fin 8 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 8, hist 0 (b-a^2)) = _
  simp only [row_8_0]
  fin_cases b <;> decide
private theorem row_8_2 (b : ZMod 8) : hist 2 b = (![8,16,16,0,8,16,0,0] : Fin 8 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 8, hist 1 (b-a^2)) = _
  simp only [row_8_1]
  fin_cases b <;> decide
private theorem row_8_3 (b : ZMod 8) : hist 3 b = (![32,96,96,64,32,96,96,0] : Fin 8 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 8, hist 2 (b-a^2)) = _
  simp only [row_8_2]
  fin_cases b <;> decide
theorem base_8 : count 4 (4 : ZMod 8) = 384 := by
  rw [exact_hist]
  change (∑ a : ZMod 8, hist 3 (4-a^2)) = _
  simp only [row_8_3]
  decide

private theorem row_16_0 (b : ZMod 16) : hist 0 b = (![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] : Fin 16 → ℕ) ⟨b.val,b.val_lt⟩ := by
  fin_cases b <;> decide
private theorem row_16_1 (b : ZMod 16) : hist 1 b = (![4,4,0,0,4,0,0,0,0,4,0,0,0,0,0,0] : Fin 16 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 16, hist 0 (b-a^2)) = _
  simp only [row_16_0]
  fin_cases b <;> decide
private theorem row_16_2 (b : ZMod 16) : hist 2 b = (![16,32,32,0,32,32,0,0,16,32,32,0,0,32,0,0] : Fin 16 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 16, hist 1 (b-a^2)) = _
  simp only [row_16_1]
  fin_cases b <;> decide
private theorem row_16_3 (b : ZMod 16) : hist 3 b = (![64,384,384,256,192,384,384,0,192,384,384,256,64,384,384,0] : Fin 16 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 16, hist 2 (b-a^2)) = _
  simp only [row_16_2]
  fin_cases b <;> decide
theorem base_16 : count 4 (4 : ZMod 16) = 3072 := by
  rw [exact_hist]
  change (∑ a : ZMod 16, hist 3 (4-a^2)) = _
  simp only [row_16_3]
  decide

private theorem row_32_0 (b : ZMod 32) : hist 0 b = (![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] : Fin 32 → ℕ) ⟨b.val,b.val_lt⟩ := by
  fin_cases b <;> decide
private theorem row_32_1 (b : ZMod 32) : hist 1 b = (![4,4,0,0,8,0,0,0,0,4,0,0,0,0,0,0,4,4,0,0,0,0,0,0,0,4,0,0,0,0,0,0] : Fin 32 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 32, hist 0 (b-a^2)) = _
  simp only [row_32_0]
  fin_cases b <;> decide
private theorem row_32_2 (b : ZMod 32) : hist 2 b = (![32,64,64,0,64,64,0,0,64,64,64,0,0,64,0,0,32,64,64,0,64,64,0,0,0,64,64,0,0,64,0,0] : Fin 32 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 32, hist 1 (b-a^2)) = _
  simp only [row_32_1]
  fin_cases b <;> decide
private theorem row_32_3 (b : ZMod 32) : hist 3 b = (![256,1536,1536,1024,768,1536,1536,0,768,1536,1536,1024,512,1536,1536,0,256,1536,1536,1024,768,1536,1536,0,768,1536,1536,1024,0,1536,1536,0] : Fin 32 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 32, hist 2 (b-a^2)) = _
  simp only [row_32_2]
  fin_cases b <;> decide
theorem base_32 : count 4 (4 : ZMod 32) = 24576 := by
  rw [exact_hist]
  change (∑ a : ZMod 32, hist 3 (4-a^2)) = _
  simp only [row_32_3]
  decide

private theorem base_all (j : ℕ) : 4*count 4 (4:ZMod (2^(j+3)))=3*(2^(j+3))^3 := by
  rcases j with _|j
  · change 4*count 4 (4:ZMod 8)=_; rw [base_8]; decide
  rcases j with _|j
  · change 4*count 4 (4:ZMod 16)=_; rw [base_16]; decide
  rw [show 2^(j+1+1+3)=32*2^j by ring,orbit_count4,base_32]
  ring

/-- At target 4^(k+1) every depth r ≥ 2k+3 has exactly the same normalized
four-square count, 3 / 4^(k+1). This is a statement of finite cardinalities. -/
theorem target_powers (k j : ℕ) :
    4^(k+1)*count 4 ((4^(k+1):ℕ):ZMod (2^(2*k+3+j)))=3*(2^(2*k+3+j))^3 := by
  induction k with
  | zero =>
    have e : 2*0+3+j=j+3 := by omega
    rw [e]; exact base_all j
  | succ k ih =>
    let m := 2^(2*k+3+j)
    let t := 4^(k+1)
    have hm : 2 ∣ m := by dsimp [m]; exact dvd_pow_self _ (by omega)
    have ht : 2 ∣ t := by dsimp [t]; exact dvd_trans (by decide : 2∣4) (dvd_pow_self _ (by omega))
    have em : 2^(2*(k+1)+3+j)=4*m := by dsimp [m]; rw [show 2*(k+1)+3+j=2+(2*k+3+j) by omega,pow_add]; rfl
    have et : 4^(k+1+1)=4*t := by dsimp [t]; ring
    rw [em,et,even_scaling m t hm ht]
    change t*count 4 ((t:ℕ):ZMod m) = 3*m^3 at ih
    linear_combination (norm := ring_nf) 64*ih

/-- Even along powers of the fixed scalar multiplier two, the family of
positive stabilized normalized counts has zero as its infimum. -/
theorem no_uniform_lower (c : ℝ) (hc : 0 < c) :
    ∃ k : ℕ, ∀ j : ℕ,
      ((count 4 ((4^(k+1):ℕ):ZMod (2^(2*k+3+j)))):ℝ) /
        ((2:ℝ)^(2*k+3+j))^3 < c := by
  obtain ⟨k,hk⟩ := exists_nat_gt (3/c)
  refine ⟨k,fun j => ?_⟩
  have eqn := target_powers k j
  have eqR : (4:ℝ)^(k+1)*(count 4 ((4^(k+1):ℕ):ZMod (2^(2*k+3+j))))=
      3*((2:ℝ)^(2*k+3+j))^3 := by exact_mod_cast eqn
  have hp : 0 < (4:ℝ)^(k+1) := by positivity
  have hpow : (k:ℝ) < (4:ℝ)^(k+1) := by
    exact_mod_cast ((Nat.lt_two_pow_self (n := k)).trans_le
      ((Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ k)).trans
       (Nat.pow_le_pow_left (by decide : 2 ≤ 4) (k+1))))
  have bound := (div_lt_iff₀ hc).mp (hk.trans hpow)
  have hD : 0 < ((2:ℝ)^(2*k+3+j))^3 := by positivity
  rw [div_lt_iff₀ hD]
  apply (lt_of_mul_lt_mul_left _ (a := (4:ℝ)^(k+1)) hp.le)
  rw [eqR]
  nlinarith [mul_lt_mul_of_pos_right bound hD]

end FourSquareControl
#print axioms FourSquareControl.target_powers
#print axioms FourSquareControl.no_uniform_lower
