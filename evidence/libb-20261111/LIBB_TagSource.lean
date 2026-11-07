import LIBB_RecordReservation
set_option autoImplicit false
noncomputable section
namespace LIBB_TagSource
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
def Local (r : NP6_StdModel.Reservation) (H : Bytes → State)
 {X : Type} (d : aspis_core.digest.Digest32 X) (hash : X) (e observed : Event) : Prop :=
 ∃ (recorded : Event) (input : NLT_NativeWindows.Input recorded),
 NLT_NativeWindows.question recorded=NLT_NativeWindows.question e ∧
 LIBB_RecordReservation.Bound r recorded input ∧
 observed=NLT_NativeWindows.window H d hash recorded input
/-- Adapted with provenance from NLT_EraseCompatible.erase: the extra
membership restriction preserves runtime tag binding through the SAME native
continuation. This is representation support, not a new caller clause. -/
theorem erase {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 {A : Type} (r : NP6_StdModel.Reservation) (p : Program Event A) (result : Result A)
 (records : List (Occurrence H d hash)) (invocation : Invocation H d hash p result records)
 (compatible : ∀ record∈records,LIBB_RecordReservation.Bound r record.entered record.input) :
 NLT_Continuation.Invocation (Local r H d hash) p result (records.map actual) := by
 induction invocation with
 | ret value => exact .ret value
 | prim_ok value next result records tail ih => exact .prim_ok value next result _ (ih compatible)
 | prim_fail error next => exact .prim_fail error next
 | prim_div next => exact .prim_div next
 | call_ok codec seed next record same value decoded result records tail ih =>
   exact NLT_Continuation.Invocation.call_ok codec seed next (actual record)
    ⟨record.entered,record.input,same,compatible record (List.mem_cons_self),rfl⟩ value decoded result _
    (ih (fun r member=>compatible r (List.mem_cons_of_mem _ member)))
 | call_fail codec seed next record same error decoded =>
   apply NLT_Continuation.Invocation.call_fail codec seed next (actual record) _ error decoded
   exact ⟨record.entered,record.input,same,compatible record (List.mem_singleton_self _),rfl⟩
 | call_div codec seed next record same decoded =>
   apply NLT_Continuation.Invocation.call_div codec seed next (actual record) _ decoded
   exact ⟨record.entered,record.input,same,compatible record (List.mem_singleton_self _),rfl⟩
/-- Uniform headline reservation, bound at reached calls only. The
returned value and ALL outer source events follow without a success premise.
The independent stopped-C04 constructor still needs its own prefix fold. -/
theorem source (r : NP6_StdModel.Reservation) (H : Bytes → State)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607) (result : R Unit)
 (records : List (Occurrence H d hash))
 (native : Invocation H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) result records)
 (bound : ∀ record∈records,LIBB_RecordReservation.Bound r record.entered record.input) :
 result=NJJ_Common.run r r (NLP_NativeMerkle.action H) (NLB_Parent.finish r)
  d pub proof ck hash none ∧
 records.map actual=(run r r (NLP_NativeMerkle.action H) (NLB_Parent.finish r)
  d pub proof ck hash none).events := by
 have reseed:=NLT_Reseed.source (.Ok ()) (.Ok ()) r r (NLP_NativeMerkle.action H)
  (NLB_Parent.finish (.Ok ())) (NLB_Parent.finish r) d pub proof ck hash
 have replay:=NLT_ReseedTransport.forward _ _ reseed result records native
 have erased:=erase r _ result records replay bound
 have cuts : ∀ e∈(eval (NKE_CommonProgram.run r r (NLP_NativeMerkle.action H)
  (NLB_Parent.finish r) d pub proof ck hash none)).events,
  ∀ observed,Local r H d hash e observed → observed=e := by
  rw [NKE_CommonEval.source]
  intro e entered observed localCut
  obtain ⟨recorded,input,question,consistent,value⟩:=localCut
  exact value.trans (LIBB_RecordReservation.step r H d pub proof ck hash len e entered
   recorded input question consistent)
 have joined:=NLT_Continuation.source _ _ cuts result _ erased
 rw [NKE_CommonEval.source,NJU_CommonObserved.source] at joined
 exact joined
#print axioms erase
#print axioms source
end LIBB_TagSource
end
