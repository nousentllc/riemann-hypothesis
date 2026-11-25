import DilateEndpoint

/-! The second odd neighborhood above the first separating precision has a
second child 2^e (1+2π). Its finite census agrees with the central child on
this moving diagonal. -/
noncomputable section
namespace RamDilate.Near

def child (r e : ℕ) : S r := (2:S r)^e*(1+2*QuadraticAlgebra.omega)

/-- The multiplier has no integral square root, even though its moving finite
count equals the central one. Reduction modulo four tests sixteen residues. -/
theorem twist_nonsquare : ¬∃ z : RamField.O, z^2=1+2*QuadraticAlgebra.omega := by
  rintro ⟨z,h⟩
  have p : RamField.digit 2 QuadraticAlgebra.omega = QuadraticAlgebra.omega := by
    apply QuadraticAlgebra.ext <;> first | exact map_zero _ | exact map_one _
  have h' := congrArg (RamField.digit 2) h
  rw [map_pow,map_add,map_one,map_mul,map_ofNat,p] at h'
  have hc : ∀ a b : ZMod 4, (⟨a,b⟩ : S 2)^2 ≠ 1+2*QuadraticAlgebra.omega := by
    decide +kernel
  exact hc (RamField.digit 2 z).re (RamField.digit 2 z).im h'

private theorem low4 :
    TargetOne.count 6 ((4:S 4)*(1+2*QuadraticAlgebra.omega))=2207613190144 := by
  let : Fintype (RamField.R 4) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  let t : RamField.R 4 := (4:S 4)*(1+2*QuadraticAlgebra.omega)
  have h := project_total (RamLift.reduce 16 2) 4 (RamLift.scalar_count 16 2) t
  have hc : projectedTotal (RamLift.reduce 16 2) t = 9042383626829824 := by decide +kernel
  exact Nat.eq_of_mul_eq_mul_right (by decide) (h.trans hc)

private theorem descent (r e : ℕ) :
    imprim (r+1) (child (r+1) (e+1)) = 64*TargetOne.count 6 (child r e) := by
  have h := Descent.double_count (n := 2^r)
    ((2:Descent.B ((2^r)*2))^e*(1+2*QuadraticAlgebra.omega))
  have p : RamLift.reduce (2^r) 2 QuadraticAlgebra.omega = QuadraticAlgebra.omega := by
    apply QuadraticAlgebra.ext <;> first | exact map_one _ | exact map_zero _
  rw [map_mul,map_pow,map_ofNat,map_add,map_one,map_mul,map_ofNat,p] at h
  rw [show child (r+1) (e+1) = 2*child (r+1) e by unfold child; ring]
  exact h

/-- The two targets need not be identified by multiplying each scalar by
one unit. Their primitive contributions agree, and mixed-precision division
compares their respective divisible contributions recursively. -/
theorem equal_counts (n : ℕ) :
    TargetOne.count 6 (child (n+4) (n+2)) = TargetOne.count 6 (2^(n+2) : S (n+4)) := by
  induction n with
  | zero =>
    unfold child
    rw [show (2:S 4)^2=4 by norm_num,low4,low4_four]
  | succ n ih =>
    let e := n+2
    let r := n+4
    change TargetOne.count 6 (child (r+1) (e+1))=TargetOne.count 6 (2^(e+1) : S (r+1))
    change TargetOne.count 6 (child r e)=TargetOne.count 6 (2^e : S r) at ih
    have dc : imprim (r+1) (2^(e+1) : S (r+1)) = 64*TargetOne.count 6 (2^e : S r) := by
      have h := imprim_double_nat r (2^e)
      push_cast at h
      convert h using 2; ring
    have pc : 8*prim (r+1) (2^(e+1))=15*den (r+1) := by
      rw [show (2^(e+1) : S (r+1))=8*2^n by dsimp [e]; ring]
      exact primitive_multiple _ (by dsimp [r]; omega) _
    have pn : 8*prim (r+1) (child (r+1) (e+1))=15*den (r+1) := by
      rw [show child (r+1) (e+1)=8*(2^n*(1+2*QuadraticAlgebra.omega)) by
        dsimp [e,child]; ring]
      exact primitive_multiple _ (by dsimp [r]; omega) _
    rw [split (r+1) (child (r+1) (e+1)),split (r+1) (2^(e+1)),descent,dc,ih]
    omega

end RamDilate.Near
namespace RamDilate

theorem near_count (e : ℕ) (he : 2≤e) :
    16^e * TargetOne.count 6 ((2:S (e+2))^e*(1+2*QuadraticAlgebra.omega)) =
      (2*16^e+2)*den (e+2) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le he
  rw [Nat.add_comm 2 n]
  change 16^(n+2)*TargetOne.count 6 (Near.child (n+4) (n+2))=(2*16^(n+2)+2)*den (n+4)
  rw [Near.equal_counts]
  have h := powers n 1
  rw [show 1+n+3=n+4 by omega] at h
  exact h

end RamDilate
#print axioms RamDilate.near_count
