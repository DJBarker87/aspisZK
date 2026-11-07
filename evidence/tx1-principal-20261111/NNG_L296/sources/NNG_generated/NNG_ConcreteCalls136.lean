import NNG_Standard136
import NNG_InstallArithmetic
import NNG_LIBClaims
import NNG_Model134
import NNG_ModelCircle
import NNG_ModelDecode
import NNG_ModelMask
import NNG_ModelTerminal
import NNG_InstallState
import NNG_InstallRecord
import NNG_InstallPayload
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ConcreteCalls136
open Aeneas Aeneas.Std Result NNG_Emitted

/-- Concrete raw opaque-call dictionary for the fresh verify_finish emission.
These are supplying CLOSED source models and carrier transports, not VLib
field instances. Reached domains and per-field graphs are proved separately. -/
def calls (env : RSL.Env) : Calls where
  c0 := NNG_StdArray.implementation
  c1 := NNG_StdMapErr.run
  c2 := NNG_Equality136.pointEq
  c3 := NNG_Equality136.qeq
  c4 := NNG_InstallArithmetic.add
  c5 := NNG_InstallArithmetic.mul
  c6 := NNG_ModelMask.call
  c7 := NNG_ModelTerminal.call
  c8 := NNG_LIBClaims.call env
  c9 := fun _ _ => .ok ()
  c10 := NNG_Model134.rounds
  c11 := NNG_Install.validatedRecord
  c12 := NNG_Install.payload
  c13 := NNG_ModelCircle.call
  c14 := NNG_Install.state
  c15 := NNG_ModelDecode.call

theorem std_fromFn (env : RSL.Env) : (@Calls.c0 (calls env)) = @NNG_StdArray.implementation := rfl
#print axioms std_fromFn
theorem std_mapErr (env : RSL.Env) : (@Calls.c1 (calls env)) = @NNG_StdMapErr.run := rfl
#print axioms std_mapErr
theorem mark (env : RSL.Env) (obs : Observer) (i : U8) : (calls env).c9 obs i = .ok () := rfl
#print axioms mark
end AspisR1.NNG_ConcreteCalls136
