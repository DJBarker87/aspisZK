import NLT_AllocationInstalled
import NLT_QueryInstalled
import NLT_FinishInstalled
import NLT_ReplyInstalled
import NLT_Chronology
import NLT_NoInvalid
import NLT_RuntimeDigest
set_option autoImplicit false
noncomputable section
namespace NLT_Root
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
/-- Complete child conclusions, not child-law hypotheses. The native relation
contains only the per-cut native inputs and raw native child subcuts. -/
def CallLaw (H : Bytes → State) (r : Occurrence H (NLT_RuntimeDigest.digest H) ()) : Prop :=
 NLT_AllocationInstalled.ResumeLaw (NLT_RuntimeDigest.digest H) () r.entered r.input ∧
 NLT_NativeFacts.ResumeScope r.entered r.input ∧
 NLT_AllocationInstalled.PendingLaw r.entered r.input ∧
 NLT_QueryInstalled.Law r.entered r.input ∧
 NLT_FinishInstalled.Law r.entered r.input ∧
 NLT_C04Installed.Law H r.detail ∧ NLT_ReplyInstalled.Law H r.detail
/-- Direct hybrid parent specification on the original argument domain. P6
native-cut semantic transport is retained explicitly as tool trust; the
relation is the forward interpretation of the pinned native windows, not a
new axiom or an assumed source endpoint. All raw representation/cut clauses
are exposed by the statement inventory printed below. -/
def RowSpec (H : Bytes → State) (pub proof ck : Slice U8) : Prop :=
 (∀ (result : R Unit) (records : List (Occurrence H (NLT_RuntimeDigest.digest H) ())),
  Invocation H (NLT_RuntimeDigest.digest H) ()
   (NLT_NativeSource.skeleton H (NLT_RuntimeDigest.digest H) pub proof ck ()) result records →
  let f:=NLT_FrameFromCuts.frame records
  result=NJJ_Common.run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
   (NLT_RuntimeDigest.digest H) pub proof ck () none ∧
  records.map actual=(run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
   (NLT_RuntimeDigest.digest H) pub proof ck () none).events ∧
  (∀ r∈records,NLT_NativeWindows.question (actual r)=NLT_NativeWindows.question r.entered) ∧
  (∀ r∈records,CallLaw H r) ∧
  (∀ inside,NLT_Chronology.completed records=some inside →
   NLP_EffectOrder.expand (NLP_C04Chronology.atEvent H) (records.map actual)=inside)) ∧
 (∀ records,¬NLT_NativeInvocation.Invalid H (NLT_RuntimeDigest.digest H) ()
  (NLT_NativeSource.skeleton H (NLT_RuntimeDigest.digest H) pub proof ck ()) records)
/-- TX2:065 root candidate. ONLY the original proof/public extents and the
explicit original-input Root0 relation are hypotheses. In particular the
Root0 producer on TX2:064 is NOT claimed here. Credit requires the next ledger
gate and the existing P6/native-window transcription interpretation. -/
theorem root (H : Bytes → State) (pub proof ck : Slice U8)
 (proofLength : proof.val.length=57607) (publicLength : pub.val.length≤1880)
 (root0 : NLP_InputDomain.Root0 ck proof) : RowSpec H pub proof ck := by
 constructor
 · intro result records native
   have source:=NLT_NativeSource.source H (NLT_RuntimeDigest.digest H) pub proof ck ()
    proofLength result records native
   refine ⟨source.1,source.2,?_,?_,?_⟩
   · exact NLT_RecordFrames.parent H (NLT_RuntimeDigest.digest H) pub proof ck () proofLength result records native
   · intro r member
     exact ⟨NLT_AllocationInstalled.resume H (NLT_RuntimeDigest.digest H) () r,
      NLT_NativeFacts.resume_scope H (NLT_RuntimeDigest.digest H) pub proof ck () proofLength publicLength result records native r member,
      NLT_AllocationInstalled.pending H (NLT_RuntimeDigest.digest H) pub proof ck () proofLength result records native r member,
      NLT_QueryInstalled.installed H (NLT_RuntimeDigest.digest H) pub proof ck () proofLength result records native r member,
      NLT_FinishInstalled.installed H (NLT_RuntimeDigest.digest H) pub proof ck () proofLength result records native r member,
      NLT_C04NativeInstalled.installed H (NLT_RuntimeDigest.digest H) pub proof ck () proofLength root0 result records native r member,
      NLT_ReplyInstalled.installed H (NLT_RuntimeDigest.digest H) pub proof ck () proofLength root0 result records native r member⟩
   · exact NLT_Chronology.installed H (NLT_RuntimeDigest.digest H) pub proof ck () proofLength root0 result records native
 · intro records bad
   exact NLT_NoInvalid.source H (NLT_RuntimeDigest.digest H) pub proof ck () proofLength records bad
set_option pp.proofs false
#print root
#print RowSpec
#print CallLaw
#print NLT_NativeInvocation.Invocation
#print NLT_NativeInvocation.Invalid
#print NLT_NativeInvocation.Occurrence
#print NLT_Subcuts.Detail
#print NLT_NativeWindows.Input
#print NLT_ParentCuts.Query
#print NLB_Parent.QueryCut
#print NLP_InputDomain.Root0
#print axioms root
end NLT_Root
