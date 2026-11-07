import LIBB_ProtocolBytes
import NLT_RuntimeDigest
set_option autoImplicit false
namespace LIBB_HashModel
open Aeneas Aeneas.Std
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- The byte/state inverse of the existing deployed digest carrier. -/
def state (out : RSL.B32) : State :=
 AspisV8R19.SqueezeOracleBridge.decodeState (LIB_Env.nativeKey out)
def H (env : RSL.Env) (message : Bytes) : State :=
 state (env.sha256 [LIBB_ProtocolBytes.host message])
def digest (env : RSL.Env) := NLT_RuntimeDigest.digest (H env)

theorem state_exact (out : RSL.B32) :
 NNC_ResumeEvents.digest (AspisV8R19.SqueezeOracleBridge.encodeState (state out)) = out := by
 unfold state
 rw [AspisV8R19.SqueezeOracleBridge.array_roundtrip]
 exact LIB_Env.key_roundtrip out
#print axioms state_exact
end LIBB_HashModel
