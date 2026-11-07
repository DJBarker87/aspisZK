import LIBB_TagStopPrefix
import NLT_C04StopReseed
import NLP_C04Effects
import NLT_C04StopPrefix
set_option autoImplicit false
noncomputable section
namespace LIBB_TagStop
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
/-- Adapted from NLT_C04StopParent using tag-bound contextual steps.
Actual native C04 aborts are transported by a PREFIX, never by asserting
the total-H returning reference fails. Its ideal suffix remains explicit. -/
theorem source_prefix (r : NP6_StdModel.Reservation) (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (len : proof.val.length=57607)
 (records : List (Occurrence H d hash)) (cut : NLT_C04Stop.Cut H)
 (stopped : NLT_C04Stop.At H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) records cut)
 (bound : ∀ record∈records,LIBB_RecordReservation.Bound r record.entered record.input) :
 ∃ reply suffix,
 (run r r (NLP_NativeMerkle.action H) (NLB_Parent.finish r)
  d pub proof ck hash none).events=records.map actual++Event.merkle cut.proof cut.prepared cut.folded reply::suffix := by
 have same:=NLT_Reseed.source (.Ok ()) (.Ok ()) r r (NLP_NativeMerkle.action H)
  (NLB_Parent.finish (.Ok ())) (NLB_Parent.finish r) d pub proof ck hash
 have replay:=NLT_C04StopReseed.forward _ _ same records cut stopped
 have cuts : ∀ e∈(eval (NKE_CommonProgram.run r r (NLP_NativeMerkle.action H)
  (NLB_Parent.finish r) d pub proof ck hash none)).events,
  ∀ observed,LIBB_TagSource.Local r H d hash e observed → observed=e := by
  rw [NKE_CommonEval.source]
  intro e entered observed localCut
  obtain ⟨recorded,input,question,consistent,value⟩:=localCut
  exact value.trans (LIBB_RecordReservation.step r H d pub proof ck hash len e entered
   recorded input question consistent)
 obtain ⟨e,suffix,events,question⟩:=LIBB_TagStopPrefix.source r _ records cut replay bound cuts
 obtain ⟨reply,rfl⟩:=NLT_C04StopPrefix.merkle_of_question e cut question
 rw [NKE_CommonEval.source] at events
 exact ⟨reply,suffix,events⟩
/-- The CLOSED child abort law is installed at THAT stopped parent continuation
without any returning child Result, model failure, or endpoint hypothesis. -/
theorem installed (r : NP6_StdModel.Reservation) (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (len : proof.val.length=57607)
 (root0 : NLP_InputDomain.Root0 ck proof) (records : List (Occurrence H d hash))
 (cut : NLT_C04Stop.Cut H)
 (stopped : NLT_C04Stop.At H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) records cut)
 (bound : ∀ record∈records,LIBB_RecordReservation.Bound r record.entered record.input) :
 NLL_Prefix.At
  (NLL_Parent.plan H cut.proof (NLP_RootCodec.parsed cut.proof (Port3_BatchStage.root1 cut.prepared))
   cut.prepared.queries 1#usize (NLL_Parent.sites (NLL_BatchSource.roots cut.prepared cut.folded))
   NKV_ParentSource.zeroI NKV_ParentSource.zeroV) (cut.inside++cut.pending.answered) cut.pending.parts ∧
 NLL_Prefix.At
  (NLL_ObservedCalls.calls H cut.proof (NLP_RootCodec.parsed cut.proof (Port3_BatchStage.root1 cut.prepared))
   cut.prepared.queries 1#usize (NLL_Parent.sites (NLL_BatchSource.roots cut.prepared cut.folded))
   NKV_ParentSource.zeroI NKV_ParentSource.zeroV).1 (cut.inside++cut.pending.answered) cut.pending.parts := by
 obtain ⟨reply,suffix,events⟩:=source_prefix r H d pub proof ck hash len records cut stopped bound
 have entered : Event.merkle cut.proof cut.prepared cut.folded reply∈
  (run r r (NLP_NativeMerkle.action H) (NLB_Parent.finish r)
   d pub proof ck hash none).events := by
  rw [events]
  exact List.mem_append_right _ List.mem_cons_self
 exact NLP_C04Effects.aborting H r r (NLB_Parent.finish r)
  d pub proof ck hash len root0 cut.proof cut.prepared cut.folded reply entered
  cut.inside cut.pending cut.child

#print axioms source_prefix
#print axioms installed
end LIBB_TagStop

end
