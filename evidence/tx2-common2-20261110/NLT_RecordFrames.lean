import NLT_NativeSource
set_option autoImplicit false
noncomputable section
namespace NLT_RecordFrames
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
/-- Forward induction also identifies each entered argument frame, not merely
the final event list. No equality between independent native/source logs is
an input. This supplies the C07 ownership/input family at its own occurrence. -/
theorem questions {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 {A : Type} (f : NLT_Interpreted.Uninstalled) (p : Program Event A) (result : Result A)
 (records : List (Occurrence H d hash)) (native : Invocation H d hash p result records)
 (compatible : ∀ r∈records,NLT_NativeWindows.Compatible f r.entered r.input)
 (cuts : ∀ e∈(eval p).events,∀ observed,NLT_EraseCompatible.Local f H d hash e observed → observed=e) :
 ∀ r∈records,NLT_NativeWindows.question (actual r)=NLT_NativeWindows.question r.entered := by
 induction native with
 | ret value => simp
 | prim_ok value next result records tail ih => exact ih compatible cuts
 | prim_fail error next => simp
 | prim_div next => simp
 | call_ok codec seed next record same value decoded result records tail ih =>
   have fixed:=cuts (codec.encode seed) (by cases seed <;> exact List.mem_cons_self) (actual record)
    ⟨record.entered,record.input,same,compatible record List.mem_cons_self,rfl⟩
   rw [fixed,codec.roundtrip] at decoded
   cases decoded
   have rest:=ih (fun r member=>compatible r (List.mem_cons_of_mem _ member))
    (fun e member observed localCut=>cuts e (List.mem_cons_of_mem _ member) observed localCut)
   intro r member
   rcases List.mem_cons.mp member with equal|member
   · subst r
     exact (congrArg NLT_NativeWindows.question fixed).trans same.symm
   · exact rest r member
 | call_fail codec seed next record same error decoded =>
   have fixed:=cuts (codec.encode seed) (by cases seed <;> exact List.mem_cons_self) (actual record)
    ⟨record.entered,record.input,same,compatible record (List.mem_singleton_self _),rfl⟩
   intro r member
   have equal:=List.mem_singleton.mp member
   subst r
   exact (congrArg NLT_NativeWindows.question fixed).trans same.symm
 | call_div codec seed next record same decoded =>
   have fixed:=cuts (codec.encode seed) (by cases seed <;> exact List.mem_cons_self) (actual record)
    ⟨record.entered,record.input,same,compatible record (List.mem_singleton_self _),rfl⟩
   intro r member
   have equal:=List.mem_singleton.mp member
   subst r
   exact (congrArg NLT_NativeWindows.question fixed).trans same.symm
/-- Parent installation derives every consistency/domain fact from its own
arguments and the SAME native cuts. -/
theorem parent (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (len : proof.val.length=57607)
 (result : R Unit) (records : List (Occurrence H d hash))
 (native : Invocation H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) result records) :
 ∀ r∈records,NLT_NativeWindows.question (actual r)=NLT_NativeWindows.question r.entered := by
 let f:=NLT_FrameFromCuts.frame records
 have ordered:=(NLT_NativeOrder.ordered _ result records native 0
  (NLT_SiteOrder.source (.Ok ()) (.Ok ()) (NLP_NativeMerkle.action H)
   (NLB_Parent.finish (.Ok ())) d pub proof ck hash)).2
 have compatible:=NLT_FrameFromCuts.compatible records ordered
 have same:=NLT_Reseed.source (.Ok ()) (.Ok ()) f.resume f.pending (NLP_NativeMerkle.action H)
  (NLB_Parent.finish (.Ok ())) (NLB_Parent.finish f.finish) d pub proof ck hash
 have replay:=NLT_ReseedTransport.forward _ _ same result records native
 apply questions f _ result records replay compatible
 rw [NKE_CommonEval.source]
 intro e entered observed localCut
 obtain ⟨recorded,input,question,consistent,value⟩:=localCut
 exact value.trans (NLT_QuestionStep.source f H d pub proof ck hash len e entered
  recorded input question consistent)
set_option pp.proofs false
#print parent
#print axioms questions
#print axioms parent
end NLT_RecordFrames
