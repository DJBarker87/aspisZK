import NLB_Windows
import NJU_ResumeRoot
set_option autoImplicit false
noncomputable section
namespace NLB_ResumePacket
open Aeneas Aeneas.Std Result VTop_Stages AspisR1
abbrev Run := NJU_Log.Run NJU_ResumeObserved.Event
 (core.result.Result (AspisR1Stage2.verifier.Prepared × AspisR1Stage2.verifier.Accumulator)
 AspisR1Stage2.verifier.Error)
abbrev Native := ∀ (r : NP6_StdModel.Reservation) {H : Type},
 AspisR1Stage2.aspis_core.digest.Digest32 H → Slice U8 → Slice U8 → Slice U8 → H → Run

/-- Full observed-run statement required from C01 at this invocation. Its
shape is the committed NKU_FineRoot.source statement (state.frame specialization),
not an equality of independently chosen final Results. It includes every
nested resume event, full replies, Reader cursors, buffers and abort prefixes.
This is a named, UNDISCHARGED intermediate packet proposition. Native domain,
physical cut interpretation and gating of NKU remain external child obligations. -/
def At (native : Native) (r : NP6_StdModel.Reservation) {H : Type}
 (d : VTop_Stages.aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H) : Prop :=
 native r (NJC_ResumeCalls.digest d) ck proof pub hash=
 NJU_ResumeObserved.run r (NJC_ResumeCalls.digest d) ck proof pub .S2 hash

def action (native : Native) (r : NP6_StdModel.Reservation) : NLB_Parent.Resume :=
 fun d ck proof pub hash => NHT_ResultPort.action (NIL_StatePort.reply
  (native r (NJC_ResumeCalls.digest d) ck proof pub hash).result)

/-- Full child packet implies its caller Result projection at the SAME inputs.
No source-only sibling proof is instantiated here as native credit. -/
theorem projection (native : Native) (r : NP6_StdModel.Reservation) {H : Type}
 (d : VTop_Stages.aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H)
 (packet : At native r d ck proof pub hash) :
 action native r d ck proof pub hash=NJJ_Common.resume r d ck proof pub .S2 hash := by
 unfold action
 rw [packet,NJU_ResumeRoot.source]
 rfl
#print projection
#print axioms projection
end NLB_ResumePacket
