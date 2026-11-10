import NND_ReturnedDomain
import RSL_TX2_241
set_option autoImplicit false
namespace NND_Tx2Values
open RSL NND_Returned RSL.TX2_241
/-- Intermediate transport obligation for the canonical NMN064 law. This is
NOT a new admitted packet; the concrete End/chronology-to-Result proof must
inhabit auth_ret on Dom064 before the A2 field is available. -/
structure Values (V : V2Lib) where
 auth : Bytes → Bytes → Bytes → Env → Except V.VErr Unit
 auth_ret : ∀ p q r env, Dom064 V (p,q,r) → Returns (V.tx2auth p q r) env (auth p q r env)

def mapError {V : V2Lib} (r : Except V.VErr Unit) : Except ProgramError Unit :=
 match r with | .ok () => .ok () | .error _ => .error .invalidInstructionData

theorem mapVErr_returned (V : V2Lib) (r : Except V.VErr Unit) (env : Env) :
 Returns (mapVErr V r) env (mapError r) := by
 cases r with
 | ok u => cases u; exact rs_pure env ()
 | error e =>
   exact seq _ _ env _ _ (rs_lift _ env _ (alloc env))
    (seq _ _ env _ _ (rs_lift _ env _ (emit env _)) (throw env _))

#print axioms mapVErr_returned
end NND_Tx2Values
