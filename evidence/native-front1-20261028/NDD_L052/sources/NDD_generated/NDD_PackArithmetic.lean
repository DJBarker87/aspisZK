import NDD_PackModel
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_PackArithmetic
open FIq_Native NDD_PackModel
abbrev Q := field.QM31
abbrev W := Array U32 4#usize

def encode (q : Q) : Result W := ok (words q)
def ref4 (a b c d : Q) : Result W :=
  NDD_Reference.pack_ref (Array.make 4#usize [words a,words b,words c,words d])
def tupleRef : Q × Q × Q × Q → Result W := fun (a,b,c,d) => ref4 a b c d

theorem arithmetic : (fun a b c d => do let q ← tail a b c d;encode q) = ref4 := by
  funext a b c d
  exact (reference_tail a b c d).symm

theorem tuple_beta : (fun a b c d => do let t ← ok (a,b,c,d);tupleRef t) = ref4 := by
  funext a b c d
  rfl
#print axioms arithmetic
#print axioms tuple_beta
end NDD_PackArithmetic
