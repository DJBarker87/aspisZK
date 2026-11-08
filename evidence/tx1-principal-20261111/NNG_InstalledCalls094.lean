import NNG_ConcreteCalls094
import NNG_CheckpointCall094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_InstalledCalls094
open Aeneas Aeneas.Std Result NMT_tx1
/-- Concrete F9 dictionary with revision4 checkpoint support. No child or
library operation remains a parameter. Reached-domain proofs are separate. -/
def calls (env : RSL.Env) : NNG_Context094.Calls :=
 NNG_ConcreteCalls094.calls env
  (fun _ p a proof publicBytes _ => NNG_CheckpointCall094.call env p a proof publicBytes)
theorem checkpoint (env : RSL.Env) {H : Type} (D : aspis_core.digest.Digest32 H)
 (p : verifier.Prepared) (a : verifier.Accumulator) (proof publicBytes : Slice U8) (h : H) :
 (calls env).c6 D p a proof publicBytes h = NNG_CheckpointCall094.call env p a proof publicBytes := rfl
#print axioms checkpoint
end AspisR1.NNG_InstalledCalls094
