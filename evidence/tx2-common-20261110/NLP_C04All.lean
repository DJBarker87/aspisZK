import NLP_C04AtActual
set_option autoImplicit false
noncomputable section
namespace NLP_C04All
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
def Clause (H : Bytes → State) : Event → Prop
 | .merkle proof p folded _ =>
   NLN.BatchPacket H proof (NLP_RootCodec.parsed proof (Port3_BatchStage.root1 p)) p folded 1#usize
 | _ => True
/-- No child Result, success, endpoint, or packet hypothesis. The actual source
binds provide every internal child domain; the extra Root0 input relation is
explicit and its external producer is still open. This is source support. -/
theorem source (H : Bytes → State) (wr rr : NP6_StdModel.Reservation)
 (merkle : Merkle) (finish : Finish) {X : Type}
 (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607) (root0Input : NLP_InputDomain.Root0 ck proof) :
 NKE_EventAll.Holds (Clause H) (run wr rr merkle finish d pub proof ck hash none) := by
 intro e entered
 cases e with
 | merkle pr p folded reply =>
   exact NLP_C04AtActual.packet H wr rr merkle finish d pub proof ck hash len root0Input pr p folded reply entered
 | resume _ _ _ _ => exact True.intro
 | powers _ _ => exact True.intro
 | inactive _ _ => exact True.intro
 | geometry _ _ _ => exact True.intro
 | pending _ _ => exact True.intro
 | query _ _ _ _ _ _ _ => exact True.intro
 | flush _ _ _ => exact True.intro
 | finish _ _ _ _ => exact True.intro
set_option pp.proofs false
#print Clause
#print source
#print axioms source
end NLP_C04All
