import NLP_C04AtActual
import NLP_NativeMerkle
set_option autoImplicit false
noncomputable section
namespace NLP_C04Effects
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- SAME C04 invocation: the child packet supplies the exact native Result,
chronological internal history and adopted rejection observation together. -/
theorem returning (H : Bytes → State) (wr rr : NP6_StdModel.Reservation) (finish : Finish)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607) (root0Input : NLP_InputDomain.Root0 ck proof)
 (pr : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) (reply : R Unit)
 (entered : Event.merkle pr p folded reply∈(run wr rr (NLP_NativeMerkle.action H) finish d pub proof ck hash none).events) :
 ∀ (history : NLL.History) (out : NLL.Reply),
 NLL_BatchSource.Invocation H pr p folded 1#usize history out →
 reply=NHT_ResultPort.action (ok out) ∧
 NLL_Parent.plan H pr (NLP_RootCodec.parsed pr (Port3_BatchStage.root1 p)) p.queries 1#usize
  (NLL_Parent.sites (NLL_BatchSource.roots p folded)) NKV_ParentSource.zeroI NKV_ParentSource.zeroV=history ∧
 NLL_ObservedCalls.calls H pr (NLP_RootCodec.parsed pr (Port3_BatchStage.root1 p)) p.queries 1#usize
  (NLL_Parent.sites (NLL_BatchSource.roots p folded)) NKV_ParentSource.zeroI NKV_ParentSource.zeroV=
  (history,NKV_ParentSource.observe (ok out)) := by
 intro history out native
 have packet:=NLP_C04AtActual.packet H wr rr (NLP_NativeMerkle.action H) finish d pub proof ck hash
  len root0Input pr p folded reply entered
 obtain ⟨value,historyLaw,observed⟩:=packet.returning history out native
 refine ⟨?_,historyLaw,observed⟩
 have call:=NKE_CommonCalls.source wr rr (NLP_NativeMerkle.action H) finish d pub proof ck hash _ entered
 change reply=NHT_ResultPort.action
  (NKV_FRef.verifier.candidate.batch_merkle (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) pr p folded 1#usize ()) at call
 rw [value] at call
 exact call
/-- Abort has only the reached internal prefix; no returned child or suffix is
required. The complete native prefix relation remains universally quantified. -/
theorem aborting (H : Bytes → State) (wr rr : NP6_StdModel.Reservation) (finish : Finish)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607) (root0Input : NLP_InputDomain.Root0 ck proof)
 (pr : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) (reply : R Unit)
 (entered : Event.merkle pr p folded reply∈(run wr rr (NLP_NativeMerkle.action H) finish d pub proof ck hash none).events) :
 ∀ (history : NLL.History) (pending : NLL.Pending),
 NLL_BatchAbort.Invocation H pr p folded 1#usize history pending →
 NLL_Prefix.At
  (NLL_Parent.plan H pr (NLP_RootCodec.parsed pr (Port3_BatchStage.root1 p)) p.queries 1#usize
   (NLL_Parent.sites (NLL_BatchSource.roots p folded)) NKV_ParentSource.zeroI NKV_ParentSource.zeroV)
  (history++pending.answered) pending.parts ∧
 NLL_Prefix.At
  (NLL_ObservedCalls.calls H pr (NLP_RootCodec.parsed pr (Port3_BatchStage.root1 p)) p.queries 1#usize
   (NLL_Parent.sites (NLL_BatchSource.roots p folded)) NKV_ParentSource.zeroI NKV_ParentSource.zeroV).1
  (history++pending.answered) pending.parts :=
 (NLP_C04AtActual.packet H wr rr (NLP_NativeMerkle.action H) finish d pub proof ck hash
  len root0Input pr p folded reply entered).aborting
set_option pp.proofs false
#print returning
#print aborting
#print axioms returning
#print axioms aborting
end NLP_C04Effects
