import NLC_Step_mapPublic
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_MapCut
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
abbrev Native := core.result.Result Q aspis_core.state_only_prefix.r0.Error → core.result.Result Q r1_wire.Error

def reference : core.result.Result Q aspis_core.state_only_prefix.r0.Error → core.result.Result Q r1_wire.Error
 | .Ok q => .Ok q
 | .Err _ => .Err r1_wire.Error.Public
/-- Reviewed scalar cut: NLC_K002 PASS / K003 matched assert_ne FAIL, same
KMX/frozen graph/lock. NLC_native.rs check_map asserts out==expected, where
independent good/value/error enumerate every valid Rust Result. No canonicality,
chosen successful child or proof-byte selector is assumed. Native source and
assertion SHA pins are in NLC_SOURCE_PINS.json and both scope receipts. -/
def Cut (native : Native) : Prop := ∀ r, native r = reference r

theorem model {H : Type} (D : aspis_core.Digest32 H)
 (r : core.result.Result Q aspis_core.state_only_prefix.r0.Error) :
 core.result.Result.map_err (FinishModel.closureFn11 D) r () = ok (reference r) := by
 cases r <;> rfl

def nativeStep {H : Type} (native : Native) (s : State H) : Code (Post H) := do
 let r ← read s.locals.terminalReply
 pure (returned s .mark3 (native r) (fun q => {s.locals with terminal:=some q}))
/-- Installs the scalar cut at the SAME state's reply slot, including missing
slot abort and all child Err values. Intermediate step association only. -/
theorem to_source {H : Type} (native : Native) (cut : Cut native)
 (s : State H) (atSite : s.next = .mapPublic) :
 run (nativeStep native s) = run (step s) := by
 rw [step_mapPublic s atSite]
 unfold nativeStep window_mapPublic
 cases reply : s.locals.terminalReply with
 | none => simp only [reply,read];rfl
 | some r =>
   cases r with
   | Ok q =>
     simp only [reply,read]
     change ([],ok (returned s .mark3 (native (.Ok q)) (fun v => {s.locals with terminal:=some v}))) = _
     rw [cut (.Ok q)]
     rfl
   | Err error =>
     simp only [reply,read]
     change ([],ok (returned s .mark3 (native (.Err error)) (fun v => {s.locals with terminal:=some v}))) = _
     rw [cut (.Err error)]
     rfl
#print axioms model
#print axioms to_source
#print to_source
end AspisR1.NLC_MapCut
end
