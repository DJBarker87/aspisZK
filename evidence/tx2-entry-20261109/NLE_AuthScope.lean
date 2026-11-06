import NLE_ParseInstall
import NLE_Length
import NHV_ReleaseOps
set_option autoImplicit false
noncomputable section
namespace NLE_AuthScope
open Aeneas Aeneas.Std Result VTop_Stages NLE_Auth
def install (ops : Ops) : Ops := {NLE_ParseInstall.install ops with op13 := NHV_ReleaseOps.mark}
theorem mark_stub_domain (phase : verifier.Phase) : NHV_ReleaseOps.mark none phase = ok () := rfl
/-- Every entered common event carries precisely the original Frame, and a
successful parser return from that SAME proof. This is an event assertion,
not a positive-row premise about a separately chosen child endpoint. -/
theorem entered {H : Type} (ops : Ops) (child : Common H) (s : State H)
 (frame : Frame H) (reply : Result Reply)
 (event : Event.common frame reply ∈ (G ops child s).events) :
 frame = s.frame ∧ ∃ value, ops.op3 s.frame.proof = ok (.Ok value) := by
 unfold G parse mark common at event
 cases h : ops.op3 s.frame.proof with
 | fail err => simp [h,Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,tryR] at event
 | div => simp [h,Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,tryR] at event
 | ok result =>
  cases result with
  | Err err => simp [h,Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,tryR] at event
  | Ok value =>
   cases marker : ops.op13 s.frame.observer .Parsed with
   | fail err => simp [h,marker,Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,tryR] at event
   | div => simp [h,marker,Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,tryR] at event
   | ok unit =>
    simp [h,marker,Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,tryR] at event
    exact ⟨event.1,⟨value,rfl⟩⟩
/-- The actual encoder Array carrier is installed into the caller state. -/
def withPublic {H : Type} (s : State H) (bytes : Array U8 1880#usize) : State H :=
 {s with frame := {s.frame with publicBytes := bytes.to_slice, observer := none}}
/-- BOTH C01 clauses are derived at every entered common call. No proof-size,
public-size, parse-success or accepted-parent hypothesis is supplied. -/
theorem common_domain {H : Type} (ops : Ops) (child : Common H) (s : State H)
 (bytes : Array U8 1880#usize) (frame : Frame H) (reply : Result Reply)
 (event : Event.common frame reply ∈ (G (install ops) child (withPublic s bytes)).events) :
 frame.proof.val.length = 57607 ∧ frame.publicBytes.val.length ≤ 1880 ∧ frame.observer = none := by
 obtain ⟨same,value,parsed⟩ := entered (install ops) child (withPublic s bytes) frame reply event
 subst frame
 have exactProof := NLE_ParseInstall.success s.frame.proof value parsed
 exact ⟨exactProof.2,(NLE_Length.public_scope bytes).2,rfl⟩
#print entered
#print common_domain
#print axioms mark_stub_domain
#print axioms entered
#print axioms common_domain
end NLE_AuthScope
