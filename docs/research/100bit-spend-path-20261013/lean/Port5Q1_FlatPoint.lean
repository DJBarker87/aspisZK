import Port5Q1_ListCells
set_option autoImplicit false
namespace AspisR1.Port5Q1_FlatPoint
open Aeneas Aeneas.Std
abbrev FP := ZMod AspisCircleGroupOrder.P

theorem transfer {A : Type} (f : A → List FP) (arity : ∀ x, (f x).length=5)
    (xs : List U32) (ys : List A) (a : A)
    (meaning : xs.map S7JoinBasisMachine.decode=ys.flatMap f)
    (i j : Nat) (hi : i<ys.length) (hj : j<5) :
    S7JoinBasisMachine.decode (xs[5*i+j]?.getD 0#u32)=
      ((f (ys[i]?.getD a))[j]?.getD 0) := by
  have eq := congrArg (fun zs : List FP => zs[5*i+j]?.getD 0) meaning
  rw [Port5Q1_ListCells.map_cell,Port5Q1_ListCells.flat_cell f arity ys i j hi hj] at eq
  rw [List.getElem?_eq_getElem hi]
  exact eq

#print axioms transfer
end AspisR1.Port5Q1_FlatPoint
