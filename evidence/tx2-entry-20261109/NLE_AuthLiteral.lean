import NLE_AuthScope
set_option autoImplicit false
noncomputable section
namespace NLE_AuthLiteral
open Aeneas Aeneas.Std Result VTop_Stages NLE_Auth
/-- Source-fold kernel with every local operation installed. Only the OPEN
common child is a parameter; there is no arbitrary Ops dictionary. -/
def G {H : Type} (child : Common H) (frame : Frame H) : Run H Reply := do
 let parsed ← NJU_Log.record (.parse frame.proof) (NLE_ParseInstall.parse frame.proof)
 tryR parsed fun _ => do
 let _ ← NJU_Log.record (.mark frame.observer) (NHV_ReleaseOps.mark frame.observer .Parsed)
 NJU_Log.record (.common frame) (child frame)
theorem installed {H : Type} (ops : Ops) (child : Common H) (s : State H) :
 NLE_Auth.G (NLE_AuthScope.install ops) child s = G child s.frame := by
 unfold NLE_Auth.G NLE_Auth.parse NLE_Auth.mark NLE_Auth.common G
 dsimp only [NLE_AuthScope.install,NLE_ParseInstall.install]
 cases parsed : NLE_ParseInstall.parse s.frame.proof with
 | fail err => simp [parsed,Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,tryR]
 | div => simp [parsed,Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,tryR]
 | ok result =>
  cases result with
  | Err err => simp [parsed,Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,tryR]
  | Ok value =>
   cases marker : NHV_ReleaseOps.mark s.frame.observer .Parsed <;>
    simp [parsed,marker,Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,tryR]
#print G
#print installed
#print axioms installed
end NLE_AuthLiteral
