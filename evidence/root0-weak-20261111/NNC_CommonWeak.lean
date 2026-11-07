import NLT_CompleteRoot
set_option autoImplicit false
noncomputable section
namespace NNC_CommonWeak
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
/-- Weak common law retains the native result, parent events and complete
resume child on its own domain. No C04 model/chronology installation is asserted. -/
def ResolvedLaw (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (result : R Unit) (records : List (Occurrence H d hash)) : Prop :=
 let f:=NLT_FrameFromCuts.frame records
 result=NJJ_Common.run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
  d pub proof ck hash none ∧
 records.map actual=(run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
  d pub proof ck hash none).events ∧
 (∀ r∈records,NLT_NativeWindows.question (actual r)=NLT_NativeWindows.question r.entered) ∧
 (∀ r∈records,NLT_AllocationInstalled.ResumeLaw d hash r.entered r.input ∧
  NLT_NativeFacts.ResumeScope r.entered r.input)
/-- An independently stopped C04 child has no parent return. Keep its source
prefix and complete resume records; do not claim C04 oracle expansion. -/
def StoppedLaw (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (records : List (Occurrence H d hash))
 (cut : NLT_C04Stop.Cut H) : Prop :=
 let f:=NLT_FrameFromCuts.frame records
 (∃ reply suffix,(run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
  d pub proof ck hash none).events=records.map actual++Event.merkle cut.proof cut.prepared cut.folded reply::suffix) ∧
 (∀ r∈records,NLT_AllocationInstalled.ResumeLaw d hash r.entered r.input ∧
  NLT_NativeFacts.ResumeScope r.entered r.input)
def Law (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) : NLT_CompleteRoot.End H d hash → Prop
 | .resolved result records => ResolvedLaw H d pub proof ck hash result records
 | .c04Stopped records cut => StoppedLaw H d pub proof ck hash records cut
def RowSpec (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) : Prop :=
 (∀ outcome,NLT_CompleteRoot.Native H d pub proof ck hash outcome → Law H d pub proof ck hash outcome) ∧
 (∀ records,¬Invalid H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) records)
theorem root (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X)
 (proofLength : proof.val.length=57607) (publicLength : pub.val.length≤1880) :
 RowSpec H d pub proof ck hash := by
 constructor
 · intro outcome native
   cases outcome with
   | resolved result records =>
     have source:=NLT_NativeSource.source H d pub proof ck hash proofLength result records native
     refine ⟨source.1,source.2,?_,?_⟩
     · exact NLT_RecordFrames.parent H d pub proof ck hash proofLength result records native
     · intro r member
       exact ⟨NLT_AllocationInstalled.resume H d hash r,
        NLT_NativeFacts.resume_scope H d pub proof ck hash proofLength publicLength result records native r member⟩
   | c04Stopped records cut =>
     refine ⟨NLT_C04StopParent.source_prefix H d pub proof ck hash proofLength records cut native,?_⟩
     intro r member
     exact ⟨NLT_AllocationInstalled.resume H d hash r,
      NLT_C04StopFacts.resume_scope H d pub proof ck hash proofLength publicLength records cut native r member⟩
 · intro records bad
   exact NLT_NoInvalid.source H d pub proof ck hash proofLength records bad
#print root
#print axioms root
end NNC_CommonWeak
