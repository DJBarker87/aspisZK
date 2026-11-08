import LIBB_V2Star
import LIBB_ObservationModel
import NMS_R2Fold241
set_option autoImplicit false
noncomputable section
namespace NMX_R7_Verify241
open RSL
attribute [local instance] Classical.propDecidable
abbrev V := LIBB_V2Star.library

/-- Source observation at the original three byte slices. Independent C04
abort prefixes remain in V.tx2auth; this graph is a selected source execution,
not a claim that the full observation law is Functional. -/
def verify (x : NMS_R2Replay241.VerifyArgs) (env : Env) : Obs (Except V.VErr Unit) :=
 if fits : LIBB_Tx2Auth.Fits x.1 x.2.1 x.2.2 then
  LIBB_Tx2EnvTrace.observation env
   (LIB_Bytes.fromBytes x.1 fits.1) (LIB_Bytes.fromBytes x.2.1 fits.2.1) (LIB_Bytes.fromBytes x.2.2 fits.2.2)
 else ⟨.abort,[]⟩

theorem packet : NMS_R2Replay241.VerifyPacket V verify := by
 intro x env domain
 change LIBB_Tx2Auth.law x.1 x.2.1 x.2.2 env (verify x env)
 unfold LIBB_Tx2Auth.law verify
 split
 · exact LIBB_ObservationModel.contains_graph env _ _ _
 · rfl
#print axioms packet
end NMX_R7_Verify241
end
