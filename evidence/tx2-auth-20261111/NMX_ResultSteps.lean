import NMX_StepCore
set_option autoImplicit false
noncomputable section
namespace NMX_ResultSteps
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel
abbrev Final := Result (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts PE)
def tryThen {A : Type} (r : Result (core.result.Result A PE)) (k : A → Final) : Final := do
 let reply ← r
 match reply with
 | .Ok a => k a
 | .Err e => ok (.Err e)

theorem rust (ops : Ops) (owners : Owners) {A : Type}
 (r : Result (core.result.Result A PE)) (es : List NLM_Auth233.Event)
 (next : A → Program Auth) :
 NMX_ValueLink.erase (NMX_ProgramLaws.continueRun (source ops owners) next (returned () es r)) =
 tryThen r (fun a => NMX_ValueLink.erase (eval (source ops owners) (next a) ())) := by
 rw [NMX_ErasureLaws.continue_rust]
 cases r with
 | fail e => rfl
 | div => rfl
 | ok reply => cases reply <;> rfl

theorem boxed (ops : Ops) (owners : Owners) {A : Type}
 (r : Result (core.result.Result A PE)) (es : List NLM_Auth233.Event)
 (owner : Nat) (next : Box A → Program Auth) :
 NMX_ValueLink.erase (NMX_ProgramLaws.continueRun (source ops owners) next
  (returned () es (boxResult owner r))) =
 tryThen r (fun a => NMX_ValueLink.erase (eval (source ops owners) (next ⟨owner,a⟩) ())) := by
 rw [NMX_ErasureLaws.continue_box]
 cases r with
 | fail e => rfl
 | div => rfl
 | ok reply => cases reply <;> rfl

theorem raw (ops : Ops) (owners : Owners) {A : Type}
 (r : Result A) (next : A → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.raw r) next) ()) =
 (r >>= fun a => NMX_ValueLink.erase (eval (source ops owners) (next a) ())) := by
 rw [NMX_StepCore.raw]
 cases r <;> rfl
#print axioms rust
#print axioms boxed
#print axioms raw
end NMX_ResultSteps
end
