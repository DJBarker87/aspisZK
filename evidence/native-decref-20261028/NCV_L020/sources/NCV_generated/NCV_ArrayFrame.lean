import NCV_ByteStep
set_option autoImplicit false
namespace NCV_ArrayFrame
open Aeneas Aeneas.Std Result

def at {A : Type} [Inhabited A] {n : Usize} (a : Array A n) (j : Nat) : A :=
  a.val[j]?.getD default

theorem set_at {A : Type} [Inhabited A] {n : Usize} (a : Array A n)
    (i : Usize) (x : A) (j : Nat) (hi : i.val<n.val) (hj : j<n.val) :
    at (a.set i x) j = if i.val=j then x else at a j := by
  have len : a.val.length=n.val := a.property
  simp only [at,Array.set,List.getElem?_eq_getElem (show j < (a.val.set i.val x).length by simpa using hj),
    List.getElem_set,List.getElem?_eq_getElem (show j<a.val.length by omega),Option.getD_some]

#print axioms set_at
end NCV_ArrayFrame
