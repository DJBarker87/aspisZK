import NNC_C04Trace
set_option autoImplicit false
noncomputable section
namespace NNC_RecordTrace
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NNC_DigestTrace NLT_NativeInvocation

/-- Each native occurrence supplies its OWN allocator selection and nested
C04 native child. Neither is recovered from another execution or a model run. -/
def FromRecord {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 (record : Occurrence H d hash) (trace : Trace) : Prop :=
 match record with
 | ⟨.resume ck proof pub _,reservation,_⟩ =>
   trace=(NNC_ResumeEvents.queries (NLT_NativeWindows.resumeRun d ck proof pub hash reservation).events).map Step.attempted
 | ⟨_,_,detail⟩ => NNC_C04Trace.FromDetail detail trace

theorem exists_record {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 (record : Occurrence H d hash) : ∃ trace, FromRecord record trace := by
 rcases record with ⟨e,input,detail⟩
 cases e <;> first | exact NNC_C04Trace.exists_trace detail | exact ⟨_,rfl⟩

/-- Flat chronological composition, retaining repeated calls and the full
failed/pending native prefix. No hash injectivity or source C04 law is used. -/
inductive Records {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X} :
 List (Occurrence H d hash) → Trace → Prop where
 | nil : Records [] []
 | cons (record : Occurrence H d hash) (rest : List (Occurrence H d hash))
   (head tail : Trace) (headSource : FromRecord record head) (next : Records rest tail) :
   Records (record::rest) (head++tail)

theorem exists_records {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 (records : List (Occurrence H d hash)) : ∃ trace, Records records trace := by
 induction records with
 | nil => exact ⟨[],.nil⟩
 | cons record rest ih =>
   obtain ⟨head,h⟩ := exists_record record
   obtain ⟨tail,t⟩ := ih
   exact ⟨head++tail,.cons record rest head tail h t⟩

/-- Decoration of a separately stopped C04: no returned child value or
continuation is introduced. All completed calls and the pending request stay. -/
def FromStop {H : Bytes → State} (cut : NLT_C04Stop.Cut H) (trace : Trace) : Prop :=
 ∃ log, NNC_C04StopEvents.Stopped H cut.proof cut.prepared.queries 1#usize
   (NLL_Parent.sites (NLL_BatchSource.roots cut.prepared cut.folded)) NKV_ParentSource.zeroI NKV_ParentSource.zeroV
   cut.inside cut.pending log ∧ trace=log.map Step.attempted++[.pending cut.pending.parts]

theorem exists_stop {H : Bytes → State} (cut : NLT_C04Stop.Cut H) : ∃ trace, FromStop cut trace := by
 obtain ⟨log,native⟩ := NNC_C04StopEvents.stopped_source cut.child
 exact ⟨log.map Step.attempted++[.pending cut.pending.parts],log,native,rfl⟩

def FromEnd {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X} :
 NLT_CompleteRoot.End H d hash → Trace → Prop
 | .resolved _ records, trace => Records records trace
 | .c04Stopped records cut, trace =>
   ∃ before stopped, Records records before ∧ FromStop cut stopped ∧ trace=before++stopped

theorem exists_end {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 (outcome : NLT_CompleteRoot.End H d hash) : ∃ trace, FromEnd outcome trace := by
 cases outcome with
 | resolved result records => exact exists_records records
 | c04Stopped records cut =>
   obtain ⟨before,source⟩ := exists_records records
   obtain ⟨stopped,child⟩ := exists_stop cut
   exact ⟨before++stopped,before,stopped,source,child,rfl⟩

#print axioms exists_record
#print axioms exists_records
#print axioms exists_stop
#print axioms exists_end
end NNC_RecordTrace
