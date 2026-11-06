import NLP_C04AtActual
import NLN_TX2_055
set_option autoImplicit false
noncomputable section
namespace NLP_C04Trees
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
/-- Install the literal TX2 batch1 tree root at each of C04's actual three
arguments; this retains the child-derived 12-index and 9216-byte gates. -/
theorem packet (H : Bytes → State) (wr rr : NP6_StdModel.Reservation)
 (merkle : Merkle) (finish : Finish) {X : Type}
 (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607) (root0Input : NLP_InputDomain.Root0 ck proof)
 (pr : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) (reply : R Unit)
 (entered : Event.merkle pr p folded reply∈(run wr rr merkle finish d pub proof ck hash none).events)
 (kind : Usize) (hk : kind.val<3) :
 NLN.TreePacket H pr (NLP_RootCodec.parsed pr (Port3_BatchStage.root1 p)) p.queries
  (Port3_NativeBatchCalls.rootAt (NLL_BatchSource.roots p folded) ⟨kind.val,hk⟩) 1#usize kind := by
 obtain ⟨same,extent,canonical⟩:=NLP_C04Query.domain wr rr merkle finish d pub proof ck hash len pr p folded reply entered
 obtain ⟨_,a,resumed,start,fields⟩:=NLB_C04Domain.source wr rr merkle finish d pub proof ck hash _ entered
 have rootsRead:=NLP_ResumeRoots.returned wr d ck proof pub hash p a resumed
 have foldedRead:=NLP_C04Folded.at_actual wr rr merkle finish d pub proof ck hash pr p folded reply entered
 subst pr
 exact NLN_TX2_055.root H proof len _ (NLP_RootCodec.wire _ _) p.queries _ kind hk canonical
  (NLP_C04Roots.bindings ck proof p folded root0Input rootsRead.1 foldedRead.2 ⟨kind.val,hk⟩)
set_option pp.proofs false
#print packet
#print axioms packet
end NLP_C04Trees
