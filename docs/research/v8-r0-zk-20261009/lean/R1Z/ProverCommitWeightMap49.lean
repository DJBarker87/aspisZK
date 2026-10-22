import R1Z.ProverCommitRawCoefficient49
import R1Z.ProverCommitRawSource49
/-! Pure ring-homomorphism transport of the seven raw rows to WideExact.
The symbolic point/carry/product laws precede the concrete field adapter. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitWeightMap49
open R0P.SemSource R0Z.HonestView AspisR0.Opening
open scoped BigOperators
variable {K L : Type} [Field K] [Field L]

theorem carry_map (f : K →+* L) (p : Fin 10 → K) (n : Nat) :
    f (succCarry p n)=succCarry (fun i => f (p i)) n := by
  induction n with
  | zero => simp only [succCarry,map_one]
  | succ n ih =>
    rw [succCarry,succCarry,map_mul,ih]
    by_cases h : n<10
    · simp only [dif_pos h]
    · simp only [dif_neg h,map_zero]

theorem successor_map (f : K →+* L) (p : Fin 10 → K) (i : Fin 10) :
    f (successorPoint p i)=successorPoint (fun j => f (p j)) i := by
  simp only [successorPoint,map_sub,map_add,map_mul,carry_map]

theorem opening_map (f : K →+* L) (p : Fin 10 → K) (i : Fin 3) (b : Fin 10) :
    f (openingPoints p i b)=openingPoints (fun j => f (p j)) i b := by
  fin_cases i
  · rfl
  · exact successor_map f p _
  · simp only [openingPoints,toR0,xor12Point]
    split_ifs <;> simp only [map_sub,map_one]

theorem eq_map (f : K →+* L) (p : Fin 10 → K) (r : Fin 1024) :
    f (eqWeight p r)=eqWeight (fun i => f (p i)) r := by
  rw [eqWeight,map_prod,eqWeight]
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs <;> simp only [map_sub,map_one]

theorem libra_map (f : K →+* L) (p : Fin 10 → K) (j : Fin 1024) :
    f (libraWeight p j)=libraWeight (fun i => f (p i)) j := by
  unfold libraWeight
  split_ifs <;> simp only [map_pow,map_zero]

theorem indicator_map (f : K →+* L) (r : Fin 1024) :
    f (indicator R0P.copyInactiveRows r)=indicator R0P.copyInactiveRows r := by
  unfold indicator
  split_ifs <;> simp only [map_one,map_zero]

#print axioms carry_map
#print axioms successor_map
#print axioms opening_map
#print axioms eq_map
#print axioms libra_map
#print axioms indicator_map
end R1Z.ProverCommitWeightMap49
