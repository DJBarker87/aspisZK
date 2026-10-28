import NDD_PackSealed
import NDD_PackArithmetic
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_PackComposition
open FIq_Native NDD_PackModel NDD_PackSealed NDD_PackArithmetic NDD_TupleContinuation

def paddingCut (values : Slice Q) : Result (Q × Q × Q × Q) :=
  concrete.run values (fun a b c d => ok (a,b,c,d))

/-- Concrete source-prefix transport; concrete_source separately links the
sealed prefix to the actual cohort body. No native association is assumed. -/
theorem source_reference (values : Slice Q) :
    (do let q ← concrete.run values tail;encode q) =
      (do let t ← paddingCut values;uncurry4 ref4 t) :=
  (concrete.bind values tail encode).trans
    ((congrArg (concrete.run values) arithmetic).trans
      ((concrete.bind values (fun a b c d => ok (a,b,c,d)) (uncurry4 ref4)).trans
        (congrArg (concrete.run values) tuple_beta)).symm)
#print axioms source_reference
end NDD_PackComposition
