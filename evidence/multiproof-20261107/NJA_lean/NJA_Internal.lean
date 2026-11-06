import NJA_External

set_option autoImplicit false
noncomputable section
namespace NJA_Internal
open Aeneas Aeneas.Std Result
abbrev K := NJA_Matrix.K
abbrev State := Fin 16 → U32

def part (s : State) : Nat :=
 (List.ofFn (fun i : Fin 15 => (s i.succ).val)).foldl (·+·) 0

theorem cast_fold (xs : List Nat) (a : Nat) :
 ((xs.foldl (·+·) a : Nat):K) = (xs.map (fun n => (n:K))).foldl (·+·) (a:K) := by
 induction xs generalizing a with
 | nil => rfl
 | cons x xs ih => simpa using ih (a+x)

theorem cast_part (s : State) : (part s:K) =
 (List.ofFn (fun i : Fin 15 => ((s i.succ).val:K))).foldl (·+·) 0 := by
 rw [part,cast_fold]
 simp

theorem shifts_bound (i : Fin 15) : R0P.poseidonInternalShifts i ≤ 16 := by
 fin_cases i <;> norm_num [R0P.poseidonInternalShifts]

theorem shifted_bound (x : U32) (i : Fin 15) :
 x.val*2^(R0P.poseidonInternalShifts i) < 2^48 := by
 have xbound := x.bv.isLt
 change x.val < 2^32 at xbound
 have bound := shifts_bound i
 have power : 2^(R0P.poseidonInternalShifts i) ≤ 2^16 := by
   fin_cases i <;> norm_num [R0P.poseidonInternalShifts]
 have nonzero : 0<2^(R0P.poseidonInternalShifts i) := by positivity
 have := Nat.mul_lt_mul_of_pos_right xbound nonzero
 have := Nat.mul_le_mul_left (2^32) power
 omega

def zeroArg (s : State) : Nat := part s+2147483647-(s 0).val

theorem zero_cast (s : State) (canonical : (s 0).val < 2147483647) :
 (zeroArg s:K) = (part s:K)-((s 0).val:K) := by
 unfold zeroArg
 rw [Nat.cast_sub (by omega : (s 0).val≤part s+2147483647)]
 simp [K,NJA_Matrix.K,AspisV8R15.ExactTowerBase.M31Exact]

def nonzeroArg (s : State) (i : Fin 16) (hi : i.val≠0) : Nat :=
 part s+(s 0).val+(s i).val*2^(R0P.poseidonInternalShifts ⟨i.val-1,by omega⟩)

theorem nonzero_cast (s : State) (i : Fin 16) (hi : i.val≠0) :
 (nonzeroArg s i hi:K) = (part s:K)+((s 0).val:K)+((s i).val:K)*
   ((1 <<< R0P.poseidonInternalShifts ⟨i.val-1,by omega⟩ : Nat):K) := by
 simp [nonzeroArg,Nat.one_shiftLeft]

theorem zero_model (s : State) (canonical : (s 0).val < 2147483647) :
 (zeroArg s:K) = R0P.poseidonInternalLinear (fun i => ((s i).val:K)) 0 := by
 rw [zero_cast s canonical,cast_part]
 simp [R0P.poseidonInternalLinear]

theorem nonzero_model (s : State) (i : Fin 16) (hi : i.val≠0) :
 (nonzeroArg s i hi:K) = R0P.poseidonInternalLinear (fun j => ((s j).val:K)) i := by
 rw [nonzero_cast,cast_part]
 have ne : i ≠ 0 := by intro h;apply hi;exact congrArg Fin.val h
 simp [R0P.poseidonInternalLinear,hi,ne]

#print axioms cast_fold
#print axioms cast_part
#print axioms shifts_bound
#print axioms shifted_bound
#print axioms zero_cast
#print axioms nonzero_cast
#print axioms zero_model
#print axioms nonzero_model
end NJA_Internal
end
