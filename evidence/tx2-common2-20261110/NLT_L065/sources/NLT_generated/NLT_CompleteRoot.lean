import NLT_AllocationInstalled
import NLT_QueryInstalled
import NLT_FinishInstalled
import NLT_ReplyInstalled
import NLT_Chronology
import NLT_NoInvalid
import NLT_C04StopFacts
import NLT_C04StopChronology
set_option autoImplicit false
noncomputable section
namespace NLT_CompleteRoot
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
/-- The original Rust generic Digest32/hash argument is preserved, including
partial runtime replies. H is the existing returning-value realization used
by the CLOSED C04 packet; no runtime totality premise is introduced. -/
inductive End (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X) (hash : X) where
 | resolved (result : R Unit) (records : List (Occurrence H d hash))
 | c04Stopped (records : List (Occurrence H d hash)) (cut : NLT_C04Stop.Cut H)
def Native (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) : End H d hash → Prop
 | .resolved result records => Invocation H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) result records
 | .c04Stopped records cut => NLT_C04Stop.At H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) records cut
def CallLaw (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X) (hash : X)
 (r : Occurrence H d hash) : Prop :=
 NLT_AllocationInstalled.ResumeLaw d hash r.entered r.input ∧
 NLT_NativeFacts.ResumeScope r.entered r.input ∧
 NLT_AllocationInstalled.PendingLaw r.entered r.input ∧
 NLT_QueryInstalled.Law r.entered r.input ∧
 NLT_FinishInstalled.Law r.entered r.input ∧
 NLT_C04Installed.Law H r.detail ∧ NLT_ReplyInstalled.Law H r.detail
/-- Resolved G cases include modeled fail/div with their exact prefixes; this
name does NOT assert that the Rust function returned normally. -/
def ResolvedLaw (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (result : R Unit) (records : List (Occurrence H d hash)) : Prop :=
 let f:=NLT_FrameFromCuts.frame records
 result=NJJ_Common.run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
  d pub proof ck hash none ∧
 records.map actual=(run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
  d pub proof ck hash none).events ∧
 (∀ r∈records,NLT_NativeWindows.question (actual r)=NLT_NativeWindows.question r.entered) ∧
 (∀ r∈records,CallLaw H d hash r) ∧
 (∀ inside,NLT_Chronology.completed records=some inside →
  NLP_EffectOrder.expand (NLP_C04Chronology.atEvent H) (records.map actual)=inside)
/-- There is NO returned native child reply or equation to a reference failure.
The ideal source reply/suffix is explicitly retained after the stopped call. -/
def StoppedLaw (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (records : List (Occurrence H d hash)) (cut : NLT_C04Stop.Cut H) : Prop :=
 let f:=NLT_FrameFromCuts.frame records
 (∃ reply suffix,(run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
  d pub proof ck hash none).events=records.map actual++Event.merkle cut.proof cut.prepared cut.folded reply::suffix) ∧
 (∀ r∈records,NLT_NativeFacts.ResumeScope r.entered r.input ∧
  NLT_AllocationInstalled.ResumeLaw d hash r.entered r.input) ∧
 NLL_Prefix.At
  (NLP_EffectOrder.expand (NLP_C04Chronology.atEvent H)
   (run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
    d pub proof ck hash none).events)
  (cut.inside++cut.pending.answered) cut.pending.parts ∧
 NLL_Prefix.At
  (NLL_ObservedCalls.calls H cut.proof (NLP_RootCodec.parsed cut.proof (Port3_BatchStage.root1 cut.prepared))
   cut.prepared.queries 1#usize (NLL_Parent.sites (NLL_BatchSource.roots cut.prepared cut.folded))
   NKV_ParentSource.zeroI NKV_ParentSource.zeroV).1
  (cut.inside++cut.pending.answered) cut.pending.parts

def Law (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) : End H d hash → Prop
 | .resolved result records => ResolvedLaw H d pub proof ck hash result records
 | .c04Stopped records cut => StoppedLaw H d pub proof ck hash records cut

def RowSpec (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) : Prop :=
 (∀ outcome,Native H d pub proof ck hash outcome → Law H d pub proof ck hash outcome) ∧
 (∀ records,¬NLT_NativeInvocation.Invalid H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) records)
/-- Corrected candidate, including the independent native C04 runtime-abort
arm. Native cut semantic transport remains existing P6/D188 option-A trust.
No source reference is asserted to fail merely because the native call aborts. -/
theorem root (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X)
 (proofLength : proof.val.length=57607) (publicLength : pub.val.length≤1880)
 (root0 : NLP_InputDomain.Root0 ck proof) : RowSpec H d pub proof ck hash := by
 constructor
 · intro outcome native
   cases outcome with
   | resolved result records =>
     have source:=NLT_NativeSource.source H d pub proof ck hash proofLength result records native
     refine ⟨source.1,source.2,?_,?_,?_⟩
     · exact NLT_RecordFrames.parent H d pub proof ck hash proofLength result records native
     · intro r member
       exact ⟨NLT_AllocationInstalled.resume H d hash r,
        NLT_NativeFacts.resume_scope H d pub proof ck hash proofLength publicLength result records native r member,
        NLT_AllocationInstalled.pending H d pub proof ck hash proofLength result records native r member,
        NLT_QueryInstalled.installed H d pub proof ck hash proofLength result records native r member,
        NLT_FinishInstalled.installed H d pub proof ck hash proofLength result records native r member,
        NLT_C04NativeInstalled.installed H d pub proof ck hash proofLength root0 result records native r member,
        NLT_ReplyInstalled.installed H d pub proof ck hash proofLength root0 result records native r member⟩
     · exact NLT_Chronology.installed H d pub proof ck hash proofLength root0 result records native
   | c04Stopped records cut =>
     refine ⟨NLT_C04StopParent.source_prefix H d pub proof ck hash proofLength records cut native,?_,?_,?_⟩
     · intro r member
       exact ⟨NLT_C04StopFacts.resume_scope H d pub proof ck hash proofLength publicLength records cut native r member,
        NLT_AllocationInstalled.resume H d hash r⟩
     · exact NLT_C04StopChronology.installed H d pub proof ck hash proofLength root0 records cut native
     · exact (NLT_C04StopParent.installed H d pub proof ck hash proofLength root0 records cut native).2
 · intro records bad
   exact NLT_NoInvalid.source H d pub proof ck hash proofLength records bad
set_option pp.proofs false
#print root
#print RowSpec
#print Native
#print Law
#print StoppedLaw
#print NLT_C04Stop.Cut
#print NLT_C04Stop.At
#print axioms root
end NLT_CompleteRoot
