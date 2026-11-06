import NLT_ParentCuts
set_option autoImplicit false
noncomputable section
namespace NLT_Interpreted
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NLB_Parent
abbrev Event := NJU_CommonObserved.Event
/-- These fields have not yet been obtained from one concrete native parent.
This type MUST NOT be treated as an admitted root hypothesis. -/
structure Uninstalled where
 resume : NP6_StdModel.Reservation
 pending : NP6_StdModel.Reservation
 finish : NP6_StdModel.Reservation
 locations : NIW_AlignFinishComposed.Locations
/-- Only the reached query occurrence requires an incoming capture. Other
sites consume no invented observations. -/
def Input : Event → Type
 | .query proof p a g geo pending _ => NLT_ParentCuts.Query ⟨proof,p,a,g,geo,pending⟩
 | _ => PUnit
/-- Every reply is computed by the installed local native G. The encoded
reply is ignored. The C07 capture is local to this exact occurrence. -/
def window (f : Uninstalled) (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 {X : Type} (d : aspis_core.digest.Digest32 X) (hash : X) (e : Event) (input : Input e) : Event :=
 match e with
 | .query pr p a g geo pending reply =>
   queryWindow (NLB_Parent.window f.pending f.finish f.locations
    (NLB_ResumePacket.action NLP_ResumeInstall.native f.resume) (NLP_NativeMerkle.action H) d hash)
    (fun _=>input.observation) (.query pr p a g geo pending reply)
 | e => flushWindow (NLB_Parent.window f.pending f.finish f.locations
    (NLB_ResumePacket.action NLP_ResumeInstall.native f.resume) (NLP_NativeMerkle.action H) d hash) e
/-- Cut inputs contain no child reply, success, or parent endpoint. This is
still an auxiliary interpreted relation, pending physical installation. -/
def Local (f : Uninstalled) (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 {X : Type} (d : aspis_core.digest.Digest32 X) (hash : X) (e actual : Event) : Prop :=
 ∃ input : Input e,actual=window f H d hash e input

theorem step (f : Uninstalled) (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607) (e : Event)
 (entered : e∈(run f.resume f.pending (NLP_NativeMerkle.action H) (finish f.finish) d pub proof ck hash none).events)
 (input : Input e) : window f H d hash e input=e := by
 cases e with
 | query pr p a g geo pending reply =>
   exact query_step f.resume f.pending f.finish f.locations
    (NLB_ResumePacket.action NLP_ResumeInstall.native f.resume)
    (NLP_NativeMerkle.action H) (NLP_NativeMerkle.action H) d pub proof ck hash
    pr p a g geo pending reply entered len (fun _=>input.observation) input.frame
 | flush pending weights reply =>
   change Event.flush pending weights (ok (NLB_NativeFlush.G pending weights))=_
   rw [NLB_NativeFlush.at_actual f.resume f.pending (NLP_NativeMerkle.action H) (finish f.finish)
    d pub proof ck hash pending weights reply entered]
 | resume c pr pu reply =>
   exact steps f.resume f.pending f.finish f.locations
    (NLB_ResumePacket.action NLP_ResumeInstall.native f.resume)
    (NLP_NativeMerkle.action H) (NLP_NativeMerkle.action H)
    (fun d c pr pu hash=>NLP_ResumeInstall.action f.resume d c pr pu hash)
    (fun _ _ _ _ _=>rfl) d pub proof ck hash _ entered
 | powers gamma reply =>
   exact C02_step f.resume f.pending f.finish f.locations
    (NLB_ResumePacket.action NLP_ResumeInstall.native f.resume)
    (NLP_NativeMerkle.action H) (NLP_NativeMerkle.action H) d pub proof ck hash gamma reply entered
 | inactive bytes reply =>
   exact C03_step f.resume f.pending f.finish f.locations
    (NLB_ResumePacket.action NLP_ResumeInstall.native f.resume)
    (NLP_NativeMerkle.action H) (NLP_NativeMerkle.action H) d pub proof ck hash bytes reply entered
 | merkle pr p root reply =>
   exact C04_step f.resume f.pending f.finish f.locations
    (NLB_ResumePacket.action NLP_ResumeInstall.native f.resume)
    (NLP_NativeMerkle.action H) (NLP_NativeMerkle.action H) d pub proof ck hash pr p root reply entered rfl
 | geometry queries next reply =>
   exact C05_step f.resume f.pending f.finish f.locations
    (NLB_ResumePacket.action NLP_ResumeInstall.native f.resume)
    (NLP_NativeMerkle.action H) (NLP_NativeMerkle.action H) d pub proof ck hash queries next reply entered
 | pending weights reply =>
   exact C06_step f.resume f.pending f.finish f.locations
    (NLB_ResumePacket.action NLP_ResumeInstall.native f.resume)
    (NLP_NativeMerkle.action H) (NLP_NativeMerkle.action H) d pub proof ck hash weights reply entered
 | finish v p a reply =>
   exact C09_step f.resume f.pending f.finish f.locations
    (NLB_ResumePacket.action NLP_ResumeInstall.native f.resume)
    (NLP_NativeMerkle.action H) (NLP_NativeMerkle.action H) d pub proof ck hash v p a reply entered
set_option pp.proofs false
#print step
#print axioms step
end NLT_Interpreted
