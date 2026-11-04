import NEU_EmitModel
set_option autoImplicit false
namespace NEU_EmitFrame
open AspisR1.S2I.ReturnData
open Aeneas Aeneas.Std
/-- A reached return-data syscall is observably not an empty event frame,
even if its returned Unit is erased. This keeps the op53 obstruction explicit. -/
theorem event_frame_changed {A E : Type} (state : State A E) (bytes : List U8) :
    (set state bytes).events ≠ state.events := by
  intro same
  change state.events ++ [.setReturnData bytes] = state.events at same
  have length := congrArg List.length same
  simp only [List.length_append, List.length_singleton] at length
  omega
#print axioms event_frame_changed
end NEU_EmitFrame
