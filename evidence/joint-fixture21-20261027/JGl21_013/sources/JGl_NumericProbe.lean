import FIq_Terminal
import JFs_PublicSerialization
import JFu_ClaimsData
import JFm_PartialAlpha
import JFm_Begin
set_option autoImplicit false
namespace AspisR1.JGl_NumericProbe
open Aeneas Aeneas.Std Result
/-- Diagnostic execution only: this is not a kernel proof of acceptance. -/
def words (q : FIp_SemanticArithmetic.MQ) : Nat × Nat × Nat × Nat :=
  (q.c0.a.val,q.c0.b.val,q.c1.a.val,q.c1.b.val)
#eval match FIq_Terminal.terminal JFs_PublicSerialization.value JFu_ClaimsData.claims
    JFm_PartialAlpha.a10 JFm_Begin.challenges with
  | .ok (.Ok q) => some (words q)
  | _ => none
end AspisR1.JGl_NumericProbe
