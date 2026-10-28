import R1Z.PV_RDB2_CBL_GenericArrayFlatten
open Aeneas Aeneas.Std
namespace R1Z.PV_CBL_GenericArrayPower
open PV_CBL_LibraryShapes
set_option autoImplicit false

def Storage (T : Type) : Nat→Type
  | 0 => Odd T (Array T 0#usize)
  | k+1 => Even T (Storage T k)

def flatten {T : Type} : (k : Nat)→Storage T k→List T
  | 0,v => PV_CBL_GenericArrayFlatten.odd (fun a => a.val) v
  | k+1,v => PV_CBL_GenericArrayFlatten.even (flatten k) v

/-- One symbolic induction handles every power-of-two generic-array shape. -/
theorem length {T : Type} (k : Nat) (v : Storage T k) :
    (flatten k v).length=2^k := by
  induction k with
  | zero =>
    simp only [flatten,PV_CBL_GenericArrayFlatten.odd,List.length_append,
      List.length_singleton,v.parent1.property,v.parent2.property]
    rfl
  | succ k ih =>
    simp only [flatten,PV_CBL_GenericArrayFlatten.even,List.length_append,ih,
      Nat.pow_succ,Nat.mul_two]

#print axioms Storage
#print axioms flatten
#print axioms length
end R1Z.PV_CBL_GenericArrayPower
