import FiniteCounts
open Finset
namespace TargetOne
private theorem massPartition {A B : Type*} [Fintype A] [Fintype B] (f : A → B) (S : Finset B) :
    Nat.card {x : A // f x ∈ S} = ∑ s ∈ S, Nat.card {x : A // f x = s} :=
  Finset.card_preimage_eq_sum_card_image_eq (f := f) (s := S) fun _ _ => Set.toFinite _

theorem scalar_lifts (k : ℕ) (b : ZMod 8) :
    Nat.card {a : ZMod (8*2^k) // red k a=b} = 2^k := by
  classical
  have sur := ZMod.castHom_surjective (show 8 ∣ 8*2^k by simp)
  have flat (c : ZMod 8) : Nat.card {a // red k a=c}=Nat.card {a // red k a=b} := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
    exact AddMonoidHom.card_fiber_eq_of_mem_range (red k).toAddMonoidHom (sur c) (sur b)
  have h := massPartition (red k) univ
  simp only [Finset.mem_univ, Nat.card_subtype_true, Nat.card_zmod] at h
  simp_rw [flat] at h
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] at h
  omega

private def tupleLifts (k : ℕ) (y : Fin 6 → ZMod 8) :
    {x : Fin 6 → ZMod (8*2^k) // (fun i => red k (x i))=y} ≃
    ((i : Fin 6) → {z : ZMod (8*2^k) // red k z=y i}) where
  toFun x i := ⟨x.1 i, congrFun x.2 i⟩
  invFun x := ⟨fun i => (x i).1, funext fun i => (x i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem count_late (k : ℕ) (b : ZMod (8*2^k)) (hb : red k b=1) :
    count 6 b = 24576*(2^k)^5 := by
  classical
  let small := univ.filter fun y : Fin 6 → ZMod 8 => sqSum y = 1
  let targets := univ.filter fun t : ZMod (8*2^k) => red k t = 1
  let r := fun (x : Fin 6 → ZMod (8*2^k)) (i : Fin 6) => red k (x i)
  have hs : small.card = 24576 := by
    simpa [count,Nat.card_eq_fintype_card,Fintype.card_subtype,small] using base_eight
  have ht : targets.card = 2^k := by
    change (Finset.univ.filter (fun t : ZMod (8*2^k) => red k t = 1)).card = _
    convert scalar_lifts k 1 using 1
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have fine : ∀ t ∈ targets, count 6 t = count 6 b := by
    intro t h
    obtain ⟨u,hu⟩ := square_unit k t (Finset.mem_filter.mp h).2
    obtain ⟨v,hv⟩ := square_unit k b hb
    rw [←hu,←hv,scaled_count,scaled_count]
  have h1 := massPartition r small
  have h2 := massPartition (@sqSum (ZMod (8*2^k)) _ 6) targets
  have hc (x : Fin 6 → ZMod (8*2^k)) : r x ∈ small ↔ sqSum x ∈ targets := by
    change _ ∈ Finset.filter _ _ ↔ _ ∈ Finset.filter _ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (∑ i, (red k (x i))^2) = 1 ↔ red k (∑ i, x i^2) = 1
    rw [map_sum]; simp only [map_pow]
  have he : Nat.card {x // r x ∈ small} = Nat.card {x : Fin 6 → ZMod (8*2^k) // sqSum x ∈ targets} :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (fun x => hc x))
  have lifts (y : Fin 6 → ZMod 8) : Nat.card {x // r x = y}=(2^k)^6 := by
    rw [Nat.card_congr (tupleLifts k y), Nat.card_pi]
    simp only [scalar_lifts,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simp_rw [lifts] at h1
  change _ = ∑ s ∈ targets, count 6 s at h2
  rw [Finset.sum_congr rfl fine] at h2
  simp only [sum_const, nsmul_eq_mul, hs,ht] at h1 h2
  have hh : 2^k * count 6 b = 2^k * (24576*(2^k)^5) := by
    calc _ = 24576*(2^k)^6 := h2.symm.trans (he.symm.trans h1)
         _ = _ := by ring
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hh

theorem count_one_at_depth (k : ℕ) :
    4*count 6 (1 : ZMod (2^(k+3))) = 3*(2^(k+3))^5 := by
  rw [show 2^(k+3)=8*2^k by ring, count_late k 1 (map_one _)]
  ring

end TargetOne
#print axioms TargetOne.count_one_at_depth
