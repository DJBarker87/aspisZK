import NMX_R6_Nonempty
import NMS_R2N_ObservationMaps
import NMX_R7_Error241
import NMX_R7_Std241
set_option autoImplicit false
noncomputable section
namespace NMX_R7_VerifierSource241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted
abbrev V := LIBB_V2Star.library
abbrev Raw := core.result.Result Unit aspis_r1_cost_probe.verifier.Error

def raw : Except V.VErr Unit → Raw
 | .ok () => .Ok ()
 | .error e => .Err (NMX_R7_Error241.raw e)

def meaning (pub proof ck : Slice U8) : RSL.Spec Raw :=
 RSL.Spec.map raw (LIBB_ObservationModel.law pub proof ck)

theorem reply (r : Except V.VErr Unit) :
 NMS_R2ErrorSource.verifierReply V NMX_R7_Error241.embed (raw r) = r := by
 cases r with
 | ok unit => cases unit; rfl
 | error e => exact congrArg Except.error (NMX_R7_Error241.right e)

/-- The complete064 source law is forwarded at the exact typed public/proof/
checkpoint slices. Caller domain proof remains at the entered call site. -/
theorem full (pub proof ck : Slice U8) :
 Simulates (NMS_R2ErrorSource.verifierReply V NMX_R7_Error241.embed)
  (meaning pub proof ck)
  (V.tx2auth (NMS_R2N_RSLScalars.bytes pub) (NMS_R2N_RSLScalars.bytes proof) (NMS_R2N_RSLScalars.bytes ck)) := by
 change Simulates _ _ (LIBB_Tx2Auth.law _ _ _)
 rw [LIBB_Tx2Auth.same]
 exact NMS_R2N_ObservationMaps.cancel raw _ reply _

theorem live (pub proof ck : Slice U8) : NMX_R6_Nonempty.Live (meaning pub proof ck) := by
 apply NMX_R6_Nonempty.mapped
 intro env
 exact ⟨_,LIBB_ObservationModel.contains_graph env pub proof ck⟩
#print axioms reply
#print axioms full
#print axioms live
end NMX_R7_VerifierSource241
end
