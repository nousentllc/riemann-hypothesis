import FourEven
open Finset TargetOne
noncomputable section
namespace DyadicWave

theorem groupSum {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) (g : B → ℕ) :
    (∑ a, g (f a)) = ∑ b, Nat.card {a // f a=b} * g b := by
  rw [← Finset.sum_fiberwise' univ f g]
  simp [Nat.card_eq_fintype_card,Fintype.card_subtype]

theorem reduceSum (k : ℕ) (g : ZMod 8 → ℕ) :
    (∑ x : ZMod (8*2^k), g (red k x)) = 2^k * ∑ b, g b := by
  rw [groupSum (red k) g,Finset.mul_sum]
  simp only [scalar_lifts]

def squareRoots {R : Type*} [CommRing R] (b : R) := Nat.card {x : R // x^2=b}

theorem oddRoots (k : ℕ) (b : ZMod (8*2^k)) (hb : red k b=1) : squareRoots b=4 := by
  classical
  have same (a : ZMod (8*2^k)) (ha : red k a=1) : squareRoots a = squareRoots (1:ZMod (8*2^k)) := by
    obtain ⟨u,hu⟩ := square_unit k a ha
    symm; apply Nat.card_congr (Equiv.subtypeEquiv u.mulLeft ?_)
    intro x
    change x^2=1 ↔ ((u:_)*x)^2=a
    rw [mul_pow,←hu]
    simpa using ((u.isUnit.pow 2).mul_right_inj (b:=x^2) (c:=1)).symm
  let g := fun a : ZMod (8*2^k) => if red k a=1 then 1 else 0
  have h := groupSum (fun x : ZMod (8*2^k) => x^2) g
  have h1 := reduceSum k (fun a : ZMod 8 => if a^2=1 then 1 else 0)
  have h8 : (∑ a : ZMod 8, if a^2=1 then 1 else 0) = 4 := by decide
  rw [h8] at h1
  have h2 := reduceSum k (fun a : ZMod 8 => if a=1 then squareRoots (1 : ZMod (8*2^k)) else 0)
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true] at h2
  change (∑ a : ZMod (8*2^k), if red k (a^2)=1 then 1 else 0) = _ at h
  simp only [map_pow] at h
  rw [h1] at h
  have step (a : ZMod (8*2^k)) : Nat.card {x : ZMod (8*2^k) // x^2=a}*g a =
       if red k a=1 then squareRoots (1 : ZMod (8*2^k)) else 0 := by
    change squareRoots a * (if red k a=1 then 1 else 0) = _
    split_ifs with ha
    · simpa using same a ha
    · simp
  simp_rw [step] at h
  rw [h2] at h
  exact (same b hb).trans (Nat.eq_of_mul_eq_mul_left (by positivity) h.symm)

theorem reduceTuples (k d : ℕ) (y : Fin d → ZMod 8) :
    Nat.card {x : Fin d → ZMod (8*2^k) // (fun i => red k (x i))=y}=(2^k)^d := by
  let e : {x : Fin d → ZMod (8*2^k) // (fun i => red k (x i))=y} ≃
           ((i : Fin d) → {z : ZMod (8*2^k) // red k z=y i}) :=
    {toFun := fun x i => ⟨x.1 i,congrFun x.2 i⟩
     invFun := fun x => ⟨fun i => (x i).1,funext fun i => (x i).2⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl}
  rw [Nat.card_congr e,Nat.card_pi]
  simp only [scalar_lifts,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem reduceCount (k d : ℕ) (b : ZMod 8) :
    (∑ s : ZMod (8*2^k), if red k s=b then count d s else 0)=(2^k)^d*count d b := by
  classical
  let r (x : Fin d → ZMod (8*2^k)) := fun i => red k (x i)
  let g (s : ZMod 8) := if s=b then 1 else 0
  have hg (x : Fin d → ZMod (8*2^k)) : red k (sqSum x)=sqSum (r x) := by simp [sqSum,r]
  have h1 := groupSum (@sqSum (ZMod (8*2^k)) _ d) (fun s => g (red k s))
  have h2 := groupSum r (fun x => g (sqSum x))
  have h3 := groupSum (@sqSum (ZMod 8) _ d) g
  have link : (∑ x : Fin d → ZMod (8*2^k), g (red k (sqSum x))) =
      ∑ x : Fin d → ZMod (8*2^k), g (sqSum (r x)) :=
    Finset.sum_congr rfl fun x _ => congrArg g (hg x)
  replace h2 := h1.symm.trans (link.trans h2)
  change (∑ x : ZMod (8*2^k), count d x*g (red k x)) = _ at h2
  simp only [r,reduceTuples,←Finset.mul_sum] at h2
  rw [h3] at h2
  simpa [g,mul_ite,count,Nat.card_eq_fintype_card] using h2

theorem oddTail (k d : ℕ) (b : ZMod (8*2^k)) :
    (∑ x : ZMod (8*2^k), if (red k x)^2=1 then count d (b-x^2) else 0)
      = 4*((2^k)^d*count d (red k b-1)) := by
  classical
  let f (s : ZMod (8*2^k)) := if red k s=1 then count d (b-s) else 0
  have h := groupSum (fun x : ZMod (8*2^k) => x^2) f
  change (∑ x : ZMod (8*2^k), if red k (x^2)=1 then count d (b-x^2) else 0) = _ at h
  simp only [map_pow] at h
  rw [h,←reduceCount,Finset.mul_sum]
  have he : (∑ s : ZMod (8*2^k), 4*(if red k s=red k b-1 then count d s else 0)) =
      ∑ s : ZMod (8*2^k), 4*(if red k (b-s)=red k b-1 then count d (b-s) else 0) := by
    symm
    exact (Equiv.subLeft b).sum_comp (fun s => 4*(if red k s=red k b-1 then count d s else 0))
  rw [he]
  apply Finset.sum_congr rfl; intro s _
  have hi : red k (b-s)=red k b-1 ↔ red k s=1 := by rw [map_sub]; abel_nf; constructor <;> intro h <;> linear_combination -h
  change squareRoots s*(if red k s=1 then count d (b-s) else 0)=_
  rw [if_congr hi rfl rfl]
  split_ifs with hs
  · rw [oddRoots k s hs]
  · simp

end DyadicWave
#print axioms DyadicWave.oddTail
