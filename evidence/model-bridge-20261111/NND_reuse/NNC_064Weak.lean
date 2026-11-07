import NNC_ResumeHeader
import NMN_064
set_option autoImplicit false
noncomputable section
namespace NNC_064Weak
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- The three OWN input extents, deliberately without Root0. -/
structure Domain {X : Type} (a : Args X) : Prop where
 proofExtent : a.proof.val.length=57607
 checkpointExtent : a.checkpoint.val.length=1768
 publicBound : a.publicBytes.val.length≤1880
/-- Complete parser outcome and weak common continuation. -/
def Law (H : Bytes → State) {X : Type} (a : Args X) : End H a → Prop
 | .parseFail e=>NLE_ParseInstall.parse a.proof=.fail e
 | .parseDiv=>NLE_ParseInstall.parse a.proof=.div
 | .parseReject e=>NLE_ParseInstall.parse a.proof=.ok (.Err e)
 | .common outcome=>NNC_CommonWeak.Law H a.digest a.publicBytes a.proof a.checkpoint a.hash outcome
/-- Weak native packet: full outer chronology, full weak child outcomes and
no invalid continuation. The native relation is NMN's certified parent cut. -/
def RowSpec {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X) : Prop :=
 (∀ outcome events,NMN_064.Native H s outcome events →
  Law H s.args outcome ∧ events=chronology H s outcome) ∧
 (∀ v,NLE_ParseInstall.parse s.args.proof=.ok (.Ok v) →
  ∀ records,¬NLT_NativeInvocation.Invalid H s.args.digest s.args.hash
   (NLT_NativeSource.skeleton H s.args.digest s.args.publicBytes s.args.proof
    s.args.checkpoint s.args.hash) records)
theorem invocation {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (domain : Domain s.args) (outcome : End H s.args) (events : List (Event Ambient X))
 (native : Invocation H s outcome events) :
 Law H s.args outcome ∧ events=chronology H s outcome := by
 cases native with
 | fail e parsed => exact ⟨parsed,by simp only [chronology,parsed]⟩
 | div parsed => exact ⟨parsed,by simp only [chronology,parsed]⟩
 | reject e parsed => exact ⟨parsed,by simp only [chronology,parsed]⟩
 | common v parsed outcome child =>
   exact ⟨(NNC_CommonWeak.root H s.args.digest s.args.publicBytes s.args.proof s.args.checkpoint
    s.args.hash domain.proofExtent domain.publicBound).1 outcome child,by simp only [chronology,parsed]⟩
/-- Root0-free weak root of the ACTUAL authenticated native parent relation.
C04 items are absent; no child law or success is an input hypothesis. -/
theorem root {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (domain : Domain s.args) : RowSpec H s := by
 constructor
 · intro outcome events native
   cases native with
   | observed parsed common parser child =>
     exact invocation H s domain _ _
      (NMN_OracleFold.installed H s parsed common (NMN_064.parser parser) child)
 · intro v parsed records
   exact (NNC_CommonWeak.root H s.args.digest s.args.publicBytes s.args.proof s.args.checkpoint
    s.args.hash domain.proofExtent domain.publicBound).2 records
/-- Success of this SAME native parent supplies the matched header. The oracle
is the already approved returning-value interpretation, not injectivity. -/
theorem accepted_header {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (domain : Domain s.args)
 (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest s.args.digest) s.args.hash H)
 (records : List (NLT_NativeInvocation.Occurrence H s.args.digest s.args.hash))
 (events : List (Event Ambient X))
 (native : NMN_064.Native H s (.common (.resolved (ok (.Ok ())) records)) events) :
 NLW_ReaderHeader.decode (MultiproofConeCanonical.bytesOf s.args.checkpoint.val)=
 some (H (MultiproofConeCanonical.bytesOf s.args.proof.val),
  H (MultiproofConeCanonical.bytesOf s.args.publicBytes.val)) := by
 have law:=(root H s domain).1 _ _ native
 obtain ⟨p,a,resumed⟩:=NNC_ResumeHeader.resume_of_ok _ _ _ _ s.args.digest s.args.publicBytes
  s.args.proof s.args.checkpoint s.args.hash law.1.1.symm
 exact NNC_ResumeHeader.header_of_resume _ s.args.digest s.args.hash H oracle
  s.args.publicBytes s.args.proof s.args.checkpoint domain.checkpointExtent p a resumed
#print Domain
#print RowSpec
#print root
#print accepted_header
#print axioms invocation
#print axioms root
#print axioms accepted_header
end NNC_064Weak
