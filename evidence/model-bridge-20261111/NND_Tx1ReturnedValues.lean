import NND_PoolReturned
import RSL_TX1_345
set_option autoImplicit false
namespace NND_Tx1ReturnedValues
open RSL NND_Returned

/-- Intermediate evaluator obligation, never an own-input clause of A1. -/
structure Values (V : VLib) (P : PreparedNew V) where
 tx1 : TX1_094.Args V → Env → Except V.VErr Bytes
 returned : ∀ a env, Returns (TX1_094.Ref V P a) env (tx1 a env)

def mapVErrValue (V : VLib) (r : Except V.VErr Bytes) : Except ProgramError Bytes :=
 match r with | .ok b => .ok b | .error _ => .error .invalidInstructionData

theorem mapVErr_returned (V : VLib) (r : Except V.VErr Bytes) (env : Env) :
 Returns (TX1_328.mapVErr V r) env (mapVErrValue V r) := by
 cases r with
 | ok b => exact rs_pure env b
 | error e =>
   apply seq _ _ env (.ok ()) _
   · exact rs_lift _ env () (emit env _)
   · exact throw env _

theorem first_returned (V : VLib) (P : PreparedNew V) (F : Values V P)
 (a : TX1_328.Args V) (env : Env) :
 Returns (TX1_328.Ref V P a) env (mapVErrValue V (F.tx1 a env)) := by
 unfold TX1_328.Ref
 exact NND_Returned.bind _ _ env (F.tx1 a env) _ (call _ _ a env _ (F.returned a env))
  (mapVErr_returned V (F.tx1 a env) env)

#print axioms mapVErr_returned
#print axioms first_returned
end NND_Tx1ReturnedValues
