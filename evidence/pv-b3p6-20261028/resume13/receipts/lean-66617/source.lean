import PV_B3P_PreparedRoot12227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false
/-- Structural model of the exact fieldless reconstruct closure's empty drop
body. LLBC closure type 37 / drop function 154 is checked separately; compiler
preservation of generated glue remains V370 / D381,D386. -/
def reconstruct_drop13 (_closure : Unit) : Result Unit := .ok ()

/-- Both the normal return cleanup and the unwind cleanup invoke that same
empty destructor. Divergence does not return to execute cleanup. -/
def reconstruct_cleanup13 {α : Type} (result : Result α) : Result α :=
  match result with
  | .ok value => do
    let _ ← reconstruct_drop13 ()
    .ok value
  | .fail error => do
    let _ ← reconstruct_drop13 ()
    .fail error
  | .div => .div

def PV_B3P_Link_prepared_closure_drop : Prop :=
  ∀ (α : Type) (result : Result α), reconstruct_cleanup13 result = result

theorem reconstruct_drop_total13 : reconstruct_drop13 () = .ok () := rfl
theorem reconstruct_drop_no_unwind13 (error : Aeneas.Std.Error) :
    reconstruct_drop13 () ≠ .fail error := by intro h; cases h
theorem reconstruct_drop_no_div13 : reconstruct_drop13 () ≠ .div := by intro h; cases h

theorem reconstruct_cleanup_binding13 {α : Type} (result : Result α) :
    reconstruct_cleanup13 result = result := by
  cases result <;> rfl

theorem prepared_closure_drop_link13 : PV_B3P_Link_prepared_closure_drop :=
  fun _ result => reconstruct_cleanup_binding13 result

/-- The closure body is token-identical to reconstruct_component after the
fn/closure binder is removed. The checked source association is structural. -/
def reconstruct_call_once13 (channels : Array U64 3#usize) : Result aspis_core.field.CM31 :=
  reconstruct_cleanup13 (reference_field.reconstruct_component channels)

theorem reconstruct_call_once_binding13 (channels : Array U64 3#usize) :
    reconstruct_call_once13 channels = reference_field.reconstruct_component channels :=
  reconstruct_cleanup_binding13 _

#print axioms reconstruct_drop_total13
#print axioms reconstruct_drop_no_unwind13
#print axioms reconstruct_drop_no_div13
#print axioms reconstruct_cleanup_binding13
#print axioms prepared_closure_drop_link13
#print axioms reconstruct_call_once_binding13
end PV_B3P_Binding13227
