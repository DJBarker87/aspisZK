import NLT_C04Stop
set_option autoImplicit false
noncomputable section
namespace NLT_C04StopPrefix
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
/-- The native stopped prefix reaches the SAME source call question. The
source's ideal reply/suffix is retained; neither is required to be a native
reply after the abort. -/
theorem source {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 {A : Type} (f : NLT_Interpreted.Uninstalled) (p : Program Event A)
 (records : List (Occurrence H d hash)) (cut : NLT_C04Stop.Cut H)
 (stopped : NLT_C04Stop.At H d hash p records cut)
 (compatible : ∀ r∈records,NLT_NativeWindows.Compatible f r.entered r.input)
 (cuts : ∀ e∈(eval p).events,∀ observed,NLT_EraseCompatible.Local f H d hash e observed → observed=e) :
 ∃ e suffix,(eval p).events=records.map actual++e::suffix ∧
  NLT_NativeWindows.question e=NLT_C04Stop.question cut := by
 induction stopped with
 | prim_ok value next records cut tail ih => exact ih compatible cuts
 | call_ok codec seed next record same value decoded records cut tail ih =>
   have fixed:=cuts (codec.encode seed) (by cases seed <;> exact List.mem_cons_self) (actual record)
    ⟨record.entered,record.input,same,compatible record List.mem_cons_self,rfl⟩
   rw [fixed,codec.roundtrip] at decoded
   cases decoded
   obtain ⟨e,suffix,events,question⟩:=ih
    (fun r member=>compatible r (List.mem_cons_of_mem _ member))
    (fun e member observed localCut=>cuts e (List.mem_cons_of_mem _ member) observed localCut)
   refine ⟨e,suffix,?_,question⟩
   change codec.encode (.ok value)::(eval (next value)).events=_
   rw [events,←fixed]
   rfl
 | stopped codec seed next cut same =>
   cases seed with
   | ok value => exact ⟨codec.encode (.ok value),(eval (next value)).events,rfl,same⟩
   | fail error => exact ⟨codec.encode (.fail error),[],rfl,same⟩
   | div => exact ⟨codec.encode .div,[],rfl,same⟩
theorem merkle_of_question {H : Bytes → State} (e : Event) (cut : NLT_C04Stop.Cut H)
 (same : NLT_NativeWindows.question e=NLT_C04Stop.question cut) :
 ∃ reply,e=Event.merkle cut.proof cut.prepared cut.folded reply := by
 rcases cut with ⟨proof,p,folded,inside,pending,child⟩
 cases e <;> cases same
 exact ⟨_,rfl⟩
set_option pp.proofs false
#print source
#print axioms source
#print axioms merkle_of_question
end NLT_C04StopPrefix
