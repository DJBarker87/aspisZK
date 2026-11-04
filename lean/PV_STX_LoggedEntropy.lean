import PV_STX_EntropyWorld
import PV_STX_Composition
set_option autoImplicit false
noncomputable section
namespace PV_STX_LoggedEntropy
open Aeneas Aeneas.Std ProverRwFull PV_STX_Code PV_STX_Machine PV_STX_World
open PV_RJ4IDB (NativeEvent)
open PV_STX_EntropyWorld (Filled Provider)
variable [ExternalTypes]

/-- Harness-local ghost log, kept separate from the observed event stream.
Every record includes the full request buffer, complete answer (including
partial error writes), and the actual before/after world. No writable static. -/
structure State where
  runtime : World
  log : List (CallRecord (Slice U8) Filled) := []

def handler (provider : Provider) : Handler PV_STX_Entropy.Request State NativeEvent :=
  fun op w =>
    match op with
    | .fill buffer =>
      let r := PV_STX_EntropyWorld.draw provider buffer w.runtime
      ⟨r.answer,⟨r.world,w.log ++ [record buffer w.runtime r]⟩,r.events⟩
    | op =>
      let r := PV_STX_EntropyWorld.handler provider op w.runtime
      ⟨r.answer,⟨r.world,w.log⟩,r.events⟩

theorem fill_recorded (provider : Provider) (buffer : Slice U8) (w : State) :
    let r := PV_STX_EntropyWorld.draw provider buffer w.runtime
    handler provider (.fill buffer) w =
      ⟨r.answer,⟨r.world,w.log ++ [record buffer w.runtime r]⟩,r.events⟩ := rfl

/-- Local caller/child substitution, following ruling (y). The second request
is made at the first child's post-world. Instantiating both primitive laws is
required; no whole-helper equality or trace is assumed. This is NOT the source
retry-loop certificate. -/
theorem two_draw_substitution (provider : Provider) (buffer : Slice U8)
    (next : Filled → Slice U8) (w : State) (first : Filled) (r : Result Filled)
    (hfirst : (handler provider (.fill buffer) w).answer = .returned (.ok first))
    (hnext : (handler provider (.fill (next first))
      (handler provider (.fill buffer) w).world).answer = .returned r) :
    run (handler provider) 3
      (.seq (.call (.fill buffer)) (fun reply => .call (.fill (next reply)))) w =
      ⟨.returned r,
       (handler provider (.fill (next first)) (handler provider (.fill buffer) w).world).world,
       (handler provider (.fill buffer) w).events ++
        (handler provider (.fill (next first)) (handler provider (.fill buffer) w).world).events⟩ :=
  PV_STX_Composition.two_calls (handler provider) (.fill buffer)
    (fun reply => .fill (next reply)) w first r hfirst hnext

#print axioms fill_recorded
#print axioms two_draw_substitution
end PV_STX_LoggedEntropy
