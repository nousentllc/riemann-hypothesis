import DilatePrimitive

/-! General primitive lifting from the coefficient quotient modulo eight.
The inherited pivot edits the first unit. The counting argument below keeps
an arbitrary coarse target, which is needed for the nonsquare companion. -/
noncomputable section
open Finset TargetOne RamLift
namespace RamDilate.CompanionPrimitive
open PrimitiveRing (C V odd)

private def rearrange (n : ℕ) (b : B n) :
    {x : V n // sqSum x.1=b} ≃ {x : Fin 6 → B n // sqSum x=b ∧ ∃ i, odd (x i)} where
  toFun x := ⟨x.1.1,x.2,x.1.2⟩
  invFun x := ⟨⟨x.1,x.2.2⟩,x.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

private abbrev π (n : ℕ) : B n := QuadraticAlgebra.omega
private theorem pi_sq (n : ℕ) : (π n)^2=2 := by
  rw [pow_two,QuadraticAlgebra.omega_mul_omega_eq_mk]; rfl
private theorem pi_nil (k : ℕ) : IsNilpotent (π (8*2^k)) := by
  have h : (2:ZMod (8*2^k))^(k+3)=0 := by
    have hnat : 2^(k+3)=8*2^k := by ring
    exact_mod_cast (show (((2^(k+3):ℕ):ZMod (8*2^k)))=0 by rw [hnat]; exact ZMod.natCast_self _)
  have hh := congrArg (algebraMap (ZMod (8*2^k)) (B (8*2^k))) h
  simp only [map_pow,map_ofNat,map_zero] at hh
  exact ⟨2*(k+3),by rw [pow_mul,pi_sq,hh]⟩

private theorem decomp {n : ℕ} [NeZero n] (z : B n) : ∃ w : B n, z = (z.re.val % 2 : ℕ) + π n * w := by
  refine ⟨⟨z.im,(z.re.val / 2 : ℕ)⟩, ?_⟩
  have h := congrArg (fun t : ℕ => (t : ZMod n)) (Nat.mod_add_div z.re.val 2)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val] at h
  apply QuadraticAlgebra.ext
  · simpa [π,QuadraticAlgebra.omega,QuadraticAlgebra.re_mul] using h.symm
  · simp [π,QuadraticAlgebra.omega,QuadraticAlgebra.im_mul]

private theorem odd_unit (k : ℕ) (z : B (8*2^k)) : odd z ↔ IsUnit z := by
  obtain ⟨w,hw⟩ := decomp z
  have hn := (Commute.all (π (8*2^k)) w).isNilpotent_mul_right (pi_nil k)
  haveI : Fact (1 < 8*2^k) := ⟨by have := Nat.two_pow_pos k; omega⟩
  constructor
  · intro h
    have h1 : z.re.val%2=1 := by unfold odd at h; omega
    rw [hw,h1,Nat.cast_one]
    exact hn.isUnit_one_add
  · contrapose!
    intro h
    have h0 : z.re.val%2=0 := by simpa [odd] using h
    rw [hw,h0,Nat.cast_zero,zero_add]
    exact hn.not_isUnit

theorem constant (k : ℕ) (b w : B (8*2^k)) :
    C (8*2^k) b = C (8*2^k) (b+8*w) := by
  classical
  let A := B (8*2^k)
  let π' := π (8*2^k)
  have h6 : π'^6=8 := by calc π'^6 = (π'^2)^3 := by ring
                               _ = 8 := by rw [pi_sq]; norm_num
  haveI : Fintype A := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  obtain ⟨e,he⟩ := Pivot.scalar_perm π' (pi_nil k) (pi_sq _) (π'*w)
  let φ : Aˣ ≃ {z : A // odd z} :=
    { toFun := fun u => ⟨u,(odd_unit k u).2 u.isUnit⟩
      invFun := fun x => ((odd_unit k x.1).1 x.2).unit
      left_inv := fun u => Units.ext ((odd_unit k u).1 ((odd_unit k u).2 u.isUnit)).unit_spec
      right_inv := fun x => Subtype.ext ((odd_unit k x.1).1 x.2).unit_spec }
  let E := Equiv.Perm.extendDomain e φ
  have hp (z : A) : odd (E z) ↔ odd z := by
    by_cases hz : odd z
    · exact iff_of_true (by rw [show E z= _ from Equiv.Perm.extendDomain_apply_subtype e φ hz]; exact (φ _).property) hz
    · rw [show E z=z from Equiv.Perm.extendDomain_apply_not_subtype e φ hz]
  have hs (z : A) (hz : odd z) : (E z)^2=z^2+8*w := by
    rw [show E z= _ from Equiv.Perm.extendDomain_apply_subtype e φ hz]
    have h := he (φ.symm ⟨z,hz⟩)
    have hz' : (φ.symm ⟨z,hz⟩ : A) = z := ((odd_unit k z).1 hz).unit_spec
    change (↑(e (φ.symm ⟨z,hz⟩)) : A)^2 = _
    rw [h,hz']
    linear_combination w*h6
  unfold C
  rw [Nat.card_congr (rearrange _ b), Nat.card_congr (rearrange _ (b+8*w))]
  exact Pivot.primitive_shift odd E hp hs b
private local instance (n : ℕ) [NeZero n] : Fintype (B n) :=
  Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
private local instance (n : ℕ) [NeZero n] : Fintype (V n) := Fintype.ofFinite _

private theorem red_val (k : ℕ) (z : ZMod (8*2^k)) :
    (TargetFour.reduce 8 (2^k) z).val=z.val%8 := by
  conv_lhs => rw [←ZMod.natCast_zmod_val z,map_natCast,ZMod.val_natCast]
private theorem red_odd (k : ℕ) (z : B (8*2^k)) :
    odd (reduce 8 (2^k) z) ↔ odd z := by
  change (TargetFour.reduce 8 (2^k) z.re).val%2≠0 ↔ _
  rw [red_val,Nat.mod_mod_of_dvd _ (by decide : 2∣8)]
  rfl
private theorem kernel_multiple (k : ℕ) (z : B (8*2^k)) (h : reduce 8 (2^k) z=0) :
    ∃ w, z=8*w := by
  have hr : z.re.val%8=0 := by
    rw [←red_val]; exact congrArg ZMod.val (congrArg QuadraticAlgebra.re h)
  have hi : z.im.val%8=0 := by
    rw [←red_val]; exact congrArg ZMod.val (congrArg QuadraticAlgebra.im h)
  refine ⟨⟨(z.re.val/8 : ℕ), (z.im.val/8 : ℕ)⟩, ?_⟩
  have er : z.re.val=8*(z.re.val/8) := by omega
  have ei : z.im.val=8*(z.im.val/8) := by omega
  apply QuadraticAlgebra.ext
  · change z.re=8*↑(z.re.val/8)+2*0*↑(z.im.val/8)
    simpa using congrArg (fun t : ℕ => (t:ZMod (8*2^k))) er
  · change z.im=8*↑(z.im.val/8)+0*↑(z.re.val/8)+0*0*↑(z.im.val/8)
    simpa using congrArg (fun t : ℕ => (t:ZMod (8*2^k))) ei

private def redVec (k : ℕ) (x : V (8*2^k)) : V 8 :=
  ⟨fun i => reduce 8 (2^k) (x.1 i), by obtain ⟨i,hi⟩ := x.2; exact ⟨i,(red_odd k _).2 hi⟩⟩

private def independent (k : ℕ) (y : V 8) :
    {x : V (8*2^k) // redVec k x=y} ≃
      ((i : Fin 6) → {z : B (8*2^k) // reduce 8 (2^k) z=y.1 i}) where
  toFun x i := ⟨x.1.1 i,congrFun (congrArg Subtype.val x.2) i⟩
  invFun x := ⟨⟨fun i => (x i).1,by
        obtain ⟨j,hj⟩ := y.2
        exact ⟨j,(red_odd k _).1 (by rwa [(x j).2])⟩⟩,Subtype.ext (funext fun i => (x i).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem lift (k : ℕ) (b : B (8*2^k)) :
    C (8*2^k) b = C 8 (reduce 8 (2^k) b)*((2^k)^2)^5 := by
  classical
  let a := reduce 8 (2^k) b
  let small := univ.filter fun y : V 8 => sqSum y.1=a
  let targets := univ.filter fun t : B (8*2^k) => reduce 8 (2^k) t=a
  have hs : small.card=C 8 a := by simp [C,small,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have ht : targets.card=(2^k)^2 := by
    change (univ.filter (fun t : B (8*2^k) => reduce 8 (2^k) t=a)).card = _
    convert scalar_count 8 (2^k) a using 1
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have fine : ∀ t ∈ targets, C (8*2^k) t = C (8*2^k) b := by
    intro t ht
    have h : reduce 8 (2^k) (t-b)=0 := by
      rw [map_sub,show reduce 8 (2^k) t=a from (Finset.mem_filter.mp ht).2,sub_self]
    obtain ⟨w,hw⟩ := kernel_multiple k (t-b) h
    rw [show t=b+8*w by linear_combination hw]
    exact (constant k b w).symm
  let f := fun x : V (8*2^k) => sqSum x.1
  have h1 := TargetFour.partitions (redVec k) small
  have h2 := TargetFour.partitions f targets
  have hc (x : V (8*2^k)) : redVec k x ∈ small ↔ f x ∈ targets := by
    change _ ∈ Finset.filter _ _ ↔ _ ∈ Finset.filter _ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    change (∑ i, (reduce 8 (2^k) (x.1 i))^2)=a ↔ reduce 8 (2^k) (∑ i,(x.1 i)^2)=a
    rw [map_sum]; simp only [map_pow]
  have he : Nat.card {x // redVec k x ∈ small}=Nat.card {x // f x ∈ targets} :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (fun x => hc x))
  have lifts (y : V 8) : Nat.card {x // redVec k x=y}=((2^k)^2)^6 := by
    rw [Nat.card_congr (independent k y), Nat.card_pi]
    simp only [scalar_count,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simp_rw [lifts] at h1
  change _ = ∑ s ∈ targets, C (8*2^k) s at h2
  rw [Finset.sum_congr rfl fine] at h2
  simp only [sum_const,nsmul_eq_mul,hs,ht] at h1 h2
  apply Nat.eq_of_mul_eq_mul_left (show 0<(2^k)^2 by positivity)
  calc _ = C 8 a*((2^k)^2)^6 := h2.symm.trans (he.symm.trans h1)
       _ = _ := by ring


/-- Every coarse primitive density identity for a polynomial target of
this shape survives at every finer coefficient depth. -/
theorem primitive_later (a v r : ℕ) (hr : 3≤r)
    (h : ∀ b : S 3, 8*prim 3 ((a:S 3)*(1+QuadraticAlgebra.omega)+(v:S 3)*b)=15*den 3)
    (b : S r) :
    8*prim r ((a:S r)*(1+QuadraticAlgebra.omega)+(v:S r)*b)=15*den r := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hr
  simp only [PrimitiveRing.card_eq] at h ⊢
  revert b
  unfold den S RamField.R
  rw [show 2^(3+k)=8*2^k by ring]
  intro b
  rw [lift]
  have p : reduce 8 (2^k) QuadraticAlgebra.omega = QuadraticAlgebra.omega := by
    apply QuadraticAlgebra.ext <;> first | exact map_one _ | exact map_zero _
  rw [map_add,map_mul,map_add,map_one,p,map_natCast,map_mul,map_natCast]
  calc
    _ = (8*C 8 ((a:B 8)*(1+QuadraticAlgebra.omega)+(v:B 8)*reduce 8 (2^k) b))*((2^k)^2)^5 := by ring
    _ = _ := by
      change ∀ b : B 8, 8*C 8 ((a:B 8)*(1+QuadraticAlgebra.omega)+(v:B 8)*b)=15*((8:ℕ)^2)^5 at h
      rw [h]
      ring

end RamDilate.CompanionPrimitive
#print axioms RamDilate.CompanionPrimitive.primitive_later
