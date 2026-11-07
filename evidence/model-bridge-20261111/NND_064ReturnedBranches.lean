import NND_064ParseTransport
import NNC_WeakSpec
set_option autoImplicit false
noncomputable section
namespace NND_064ReturnedBranches
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def reply : core.result.Result Unit verifier.Error → Except verifier.Error Unit
 | .Ok u => .ok u | .Err e => .error e

/-- Ok AND Err: a returned RSL arm cannot arise from parse-fail/divergence,
modeled common-fail/divergence, or the independent stopped C04 arm. -/
theorem returned_cases (H : Bytes → State) {X : Type} (a : Args X) (outcome : End H a)
 (r : Except verifier.Error Unit) (hr : NNC_WeakSpec.exit H a outcome = .ret r) :
 (∃ e, outcome = .parseReject e ∧ r = .error e) ∨
 (∃ v records, outcome = .common (.resolved (ok v) records) ∧ r = reply v) := by
 cases outcome with
 | parseFail e => cases hr
 | parseDiv => cases hr
 | parseReject e => cases hr; exact Or.inl ⟨e,rfl,rfl⟩
 | common common =>
   cases common with
   | c04Stopped records cut => cases hr
   | resolved result records =>
     cases result with
     | fail e => cases hr
     | div => cases hr
     | ok v =>
       cases v with
       | Ok u => cases u; cases hr; exact Or.inr ⟨.Ok (),records,rfl,rfl⟩
       | Err e => cases hr; exact Or.inr ⟨.Err e,records,rfl,rfl⟩

theorem parse_reject {F C X : Type} (c : DrvC_Installation.Configuration F C)
 (H : Bytes → State) (a : Args X) (e : verifier.Error)
 (law : Law H a (.parseReject e)) :
 (DrvC_Installation.sdk c).op11 a.digest a.publicBytes a.proof a.checkpoint a.hash none = ok (.Err e) := by
 rw [NND_064ParseTransport.sdk_op11]
 unfold verifier.candidate.tx2_authenticated
 rw [NND_064ParseTransport.stage_parse]
 change NLE_ParseInstall.parse a.proof = _ at law
 rw [law]
 rfl

theorem parse_fail {F C X : Type} (c : DrvC_Installation.Configuration F C)
 (H : Bytes → State) (a : Args X) (e : Aeneas.Std.Error)
 (law : Law H a (.parseFail e)) :
 (DrvC_Installation.sdk c).op11 a.digest a.publicBytes a.proof a.checkpoint a.hash none = .fail e := by
 rw [NND_064ParseTransport.sdk_op11]
 unfold verifier.candidate.tx2_authenticated
 rw [NND_064ParseTransport.stage_parse]
 change NLE_ParseInstall.parse a.proof = _ at law
 rw [law]
 rfl

theorem parse_div {F C X : Type} (c : DrvC_Installation.Configuration F C)
 (H : Bytes → State) (a : Args X) (law : Law H a .parseDiv) :
 (DrvC_Installation.sdk c).op11 a.digest a.publicBytes a.proof a.checkpoint a.hash none = .div := by
 rw [NND_064ParseTransport.sdk_op11]
 unfold verifier.candidate.tx2_authenticated
 rw [NND_064ParseTransport.stage_parse]
 change NLE_ParseInstall.parse a.proof = _ at law
 rw [law]
 rfl

#print axioms returned_cases
#print axioms parse_reject
#print axioms parse_fail
#print axioms parse_div
end NND_064ReturnedBranches
