import NMX_ValueLink
import NMX_ProgramLaws
set_option autoImplicit false
noncomputable section
namespace NMX_ErasureLaws
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ProgramLaws
/-- Small monadic erasure laws: split one arbitrary reply, never a whole
buffer. All failure and divergence cases are included. -/
theorem continue_rust {A : Type} (handler : Handler Unit NLM_Auth233.Event)
 (next : A → Program Auth) (es : List NLM_Auth233.Event)
 (r : Result (core.result.Result A PE)) :
 NMX_ValueLink.erase (continueRun handler next (returned () es r)) =
 match r with
 | .ok (.Ok a) => NMX_ValueLink.erase (eval handler (next a) ())
 | .ok (.Err e) => .ok (.Err e)
 | .fail e => .fail e
 | .div => .div := by
 cases r with
 | fail e => rfl
 | div => rfl
 | ok reply =>
   cases reply with
   | Err e => rfl
   | Ok a => exact NMX_ValueLink.erase_prepend es _

theorem continue_raw {A : Type} (handler : Handler Unit NLM_Auth233.Event)
 (next : A → Program Auth) (es : List NLM_Auth233.Event) (r : Result A) :
 NMX_ValueLink.erase (continueRun handler next (returned () es (rawResult r))) =
 match r with
 | .ok a => NMX_ValueLink.erase (eval handler (next a) ())
 | .fail e => .fail e
 | .div => .div := by
 cases r with
 | fail e => rfl
 | div => rfl
 | ok a => exact NMX_ValueLink.erase_prepend es _

theorem continue_box {A : Type} (handler : Handler Unit NLM_Auth233.Event)
 (next : Box A → Program Auth) (es : List NLM_Auth233.Event)
 (owner : Nat) (r : Result (core.result.Result A PE)) :
 NMX_ValueLink.erase (continueRun handler next (returned () es (boxResult owner r))) =
 match r with
 | .ok (.Ok a) => NMX_ValueLink.erase (eval handler (next ⟨owner,a⟩) ())
 | .ok (.Err e) => .ok (.Err e)
 | .fail e => .fail e
 | .div => .div := by
 cases r with
 | fail e => rfl
 | div => rfl
 | ok reply =>
   cases reply with
   | Err e => rfl
   | Ok a => exact NMX_ValueLink.erase_prepend es _
#print axioms continue_rust
#print axioms continue_raw
#print axioms continue_box
end NMX_ErasureLaws
end
