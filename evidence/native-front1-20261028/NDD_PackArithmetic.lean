import NDD_PackModel
import NDD_TupleContinuation
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_PackArithmetic
open FIq_Native NDD_PackModel NDD_TupleContinuation
abbrev Q := field.QM31
abbrev W := Array U32 4#usize

def encode (q : Q) : Result W := ok (words q)
def ref4 (a b c d : Q) : Result W :=
  NDD_Reference.pack_ref (Array.make 4#usize [words a,words b,words c,words d])

theorem arithmetic : (fun a b c d => do let q ← tail a b c d;encode q) = ref4 := by
  funext a b c d
  exact (reference_tail a b c d).symm

theorem tuple_beta :
    (fun a b c d => do let t ← ok (a,b,c,d);uncurry4 ref4 t) = ref4 :=
  (bind_tuple (uncurry4 ref4)).trans (curry_uncurry ref4)
#print axioms arithmetic
#print axioms tuple_beta
end NDD_PackArithmetic
