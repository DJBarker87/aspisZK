import R1Z.ProverRw21FlatOutput
set_option autoImplicit false
namespace R1Z.ProverRw21FlatSequence
open Aeneas Aeneas.Std
abbrev W := ProverRw21FlatOutput.W

def bytes (values : List W) : List U8 := values.flatMap ProverRw21FlatOutput.bytes

theorem length (values : List W) : (bytes values).length=32*values.length := by
  induction values with
  | nil => rfl
  | cons x xs ih =>
    simp only [bytes,List.flatMap_cons,List.length_append,ProverRw21FlatOutput.length,
      List.length_cons] at *
    omega

theorem append (xs ys : List W) : bytes (xs++ys)=bytes xs++bytes ys := by
  exact List.flatMap_append

theorem suffix (values : List W) (i : Nat) (h : i<values.length) :
    bytes (values.drop i) = ProverRw21FlatOutput.bytes values[i] ++ bytes (values.drop (i+1)) := by
  rw [List.drop_eq_getElem_cons h]
  rfl

#print axioms length
#print axioms append
#print axioms suffix
end R1Z.ProverRw21FlatSequence
