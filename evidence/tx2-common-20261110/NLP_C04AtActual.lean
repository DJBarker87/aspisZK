import NLP_C04Query
import NLP_C04Roots
import NLP_C04Folded
import NLB_C04Domain
set_option autoImplicit false
noncomputable section
namespace NLP_C04AtActual
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Every child domain is discharged at the actual C04 event, conditional
only on named original-input clauses. Root0's TX2:064 producer remains open. -/
theorem packet (H : Bytes → State) (wr rr : NP6_StdModel.Reservation)
 (merkle : Merkle) (finish : Finish) {X : Type}
 (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607) (root0Input : NLP_InputDomain.Root0 ck proof)
 (pr : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) (reply : R Unit)
 (entered : Event.merkle pr p folded reply∈(run wr rr merkle finish d pub proof ck hash none).events) :
 NLN.BatchPacket H pr (NLP_RootCodec.parsed pr (Port3_BatchStage.root1 p)) p folded 1#usize := by
 obtain ⟨same,extent,canonical⟩:=NLP_C04Query.domain wr rr merkle finish d pub proof ck hash len pr p folded reply entered
 obtain ⟨_,a,resumed,start,fields⟩:=NLB_C04Domain.source wr rr merkle finish d pub proof ck hash _ entered
 have rootsRead:=NLP_ResumeRoots.returned wr d ck proof pub hash p a resumed
 have foldedRead:=NLP_C04Folded.at_actual wr rr merkle finish d pub proof ck hash pr p folded reply entered
 subst pr
 exact NLN_TX2_053.root H proof len _ (NLP_RootCodec.wire _ _) p folded canonical
  (NLP_C04Roots.bindings ck proof p folded root0Input rootsRead.1 foldedRead.2)
set_option pp.proofs false
#print packet
#print axioms packet
end NLP_C04AtActual
