import AllDepth
open Finset TargetOne
noncomputable section
namespace TargetFour
abbrev reduce (n t : ℕ) := ZMod.castHom (dvd_mul_right n t) (ZMod n)
theorem partitions {A B : Type*} [Fintype A] [Fintype B] (f : A → B) (s : Finset B) :
    Nat.card {x : A // f x ∈ s} = ∑ y ∈ s, Nat.card {x : A // f x=y} :=
  Finset.card_preimage_eq_sum_card_image_eq (f := f) (s := s) fun _ _ => Set.toFinite _

theorem scalar_count (n t : ℕ) [NeZero n] [NeZero t] (b : ZMod n) :
    Nat.card {a : ZMod (n*t) // reduce n t a=b}=t := by
  classical
  have sur := ZMod.castHom_surjective (dvd_mul_right n t)
  have flat (c : ZMod n) : Nat.card {a // reduce n t a=c} = Nat.card {a // reduce n t a=b} := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
    exact AddMonoidHom.card_fiber_eq_of_mem_range (reduce n t).toAddMonoidHom (sur c) (sur b)
  have h := partitions (reduce n t) univ
  simp only [Finset.mem_univ,Nat.card_subtype_true,Nat.card_zmod] at h
  simp_rw [flat] at h
  simp only [Finset.sum_const, Finset.card_univ,ZMod.card,nsmul_eq_mul] at h
  exact Nat.eq_of_mul_eq_mul_left (NeZero.pos n) h.symm

private def independent (n t : ℕ) (y : Fin 6 → ZMod n) :
    {x : Fin 6 → ZMod (n*t) // (fun i => reduce n t (x i))=y} ≃
      ((i : Fin 6) → {z : ZMod (n*t) // reduce n t z=y i}) where
  toFun x i := ⟨x.1 i,congrFun x.2 i⟩
  invFun x := ⟨fun i => (x i).1,funext fun i => (x i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem scaled {R : Type*} [CommRing R] (u : Rˣ) (a : R) :
    count 6 ((u:R)^2*a) = count 6 a := by
  symm
  let e := Equiv.piCongrRight fun _ : Fin 6 => u.mulLeft
  apply Nat.card_congr (Equiv.subtypeEquiv e ?_)
  intro x
  have he : sqSum (e x)=(u:R)^2*sqSum x := by
    change (∑ i, ((u:R)*x i)^2) = _ * (∑ i, x i^2)
    simp [Finset.mul_sum,mul_pow]
  rw [he]
  exact ((u.isUnit.pow 2).mul_right_inj).symm

theorem factor (k : ℕ) (b : ZMod (32*2^k)) (hb : reduce 32 (2^k) b = 4) :
    ∃ u : (ZMod (32*2^k))ˣ, b=(u:ZMod (32*2^k))^2*4 := by
  have he : ((b.val : ℕ) : ZMod 32)=4 := by
    rw [← ZMod.natCast_zmod_val b] at hb
    simpa using hb
  have hmod : b.val % 32=4 := (ZMod.natCast_eq_natCast_iff b.val 4 32).mp he
  let t := b.val / 32
  have hbv : b.val = (1+8*t)*4 := by dsimp [t]; omega
  have root (t : ℕ) : ∃ u : (ZMod (32*2^k))ˣ, (u:ZMod (32*2^k))^2=((1+8*t : ℕ) : ZMod (32*2^k)) := by
    rw [show 32*2^k=8*2^(k+2) by ring]
    apply TargetOne.square_unit
    rw [map_natCast]
    push_cast
    have hz : (8 : ZMod 8)=0 := by decide
    rw [hz,zero_mul,add_zero]
  obtain ⟨u,hu⟩ := root t
  refine ⟨u,?_⟩
  rw [hu]
  calc b = (b.val : ZMod (32*2^k)) := (ZMod.natCast_zmod_val b).symm
       _ = _ := by rw [hbv,Nat.cast_mul]; rfl

theorem orbit_count (k : ℕ) :
    count 6 (4 : ZMod (32*2^k)) = count 6 (4 : ZMod 32)*(2^k)^5 := by
  classical
  let small := univ.filter fun y : Fin 6 → ZMod 32 => sqSum y=4
  let targets := univ.filter fun t : ZMod (32*2^k) => reduce 32 (2^k) t=4
  let r := fun (x : Fin 6 → ZMod (32*2^k)) (i : Fin 6) => reduce 32 (2^k) (x i)
  have hs : small.card=count 6 (4:ZMod 32) := by simp [count,small,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have ht : targets.card=2^k := by
    change (univ.filter (fun t : ZMod (32*2^k) => reduce 32 (2^k) t=4)).card = _
    convert scalar_count 32 (2^k) 4 using 1
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have fine : ∀ t ∈ targets, count 6 t = count 6 (4:ZMod (32*2^k)) := by
    intro t ht
    obtain ⟨u,hu⟩ := factor k t (Finset.mem_filter.mp ht).2
    rw [hu,scaled]
  have h1 := partitions r small
  have h2 := partitions (@sqSum (ZMod (32*2^k)) _ 6) targets
  have hc (x : Fin 6 → ZMod (32*2^k)) : r x ∈ small ↔ sqSum x ∈ targets := by
    change _ ∈ Finset.filter _ _ ↔ _ ∈ Finset.filter _ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    change (∑ i, (reduce 32 (2^k) (x i))^2)=4 ↔ reduce 32 (2^k) (∑ i,x i^2)=4
    rw [map_sum]; simp only [map_pow]
  have he : Nat.card {x // r x ∈ small}=Nat.card {x : Fin 6 → ZMod (32*2^k) // sqSum x ∈ targets} :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (fun x => hc x))
  have lifts (y : Fin 6 → ZMod 32) : Nat.card {x // r x=y}=(2^k)^6 := by
    rw [Nat.card_congr (independent 32 (2^k) y), Nat.card_pi]
    simp only [scalar_count,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simp_rw [lifts] at h1
  change _ = ∑ s ∈ targets, count 6 s at h2
  rw [Finset.sum_congr rfl fine] at h2
  simp only [sum_const,nsmul_eq_mul,hs,ht] at h1 h2
  apply Nat.eq_of_mul_eq_mul_left (show 0<2^k by positivity)
  calc _ = count 6 (4:ZMod 32)*(2^k)^6 := h2.symm.trans (he.symm.trans h1)
       _ = _ := by ring
end TargetFour
#print axioms TargetFour.orbit_count
