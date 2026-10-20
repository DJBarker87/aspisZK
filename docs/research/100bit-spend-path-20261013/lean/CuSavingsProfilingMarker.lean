import AspisR1Profiling.Funs
/-! The actual source observer dispatcher. This target proves the local erasure
rule only. `erasedDiagnostic` is the post-projection meaning of a successful,
returning diagnostic callback; binding the fixed Solana callback and every
observer-sensitive caller to that meaning remains a separate obligation. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsProfilingMarker
open Aeneas Aeneas.Std Result AspisR1Profiling

def erasedDiagnostic (_ : Phase) : Result Unit := .ok ()

theorem marker_none (phase : Phase) : mark none phase = .ok () := rfl

theorem marker_erased (phase : Phase) :
    mark (some erasedDiagnostic) phase = mark none phase := rfl

/-- Result equality includes successful outputs, source errors, and divergence
of the arbitrary common continuation. No success premise is imposed on it. -/
theorem continuation_eq {A : Type} (phase : Phase) (suffix : Unit → Result A) :
    (mark (some erasedDiagnostic) phase >>= suffix) =
      (mark none phase >>= suffix) := rfl

/-- Every enclosing computation/observation preserves the local dispatcher
identity, once actual diagnostic semantics has been bound to erasedDiagnostic. -/
theorem context_eq {A : Type} (phase : Phase) (context : Result Unit → A) :
    context (mark (some erasedDiagnostic) phase) = context (mark none phase) := rfl

/-- Arbitrary observers are not interchangeable: a failing callback changes
Result semantics. This makes the source/runtime callback obligation explicit. -/
theorem failing_callback_not_erased (phase : Phase) (error : Error) :
    mark (some (fun _ => .fail error)) phase ≠ mark none phase := by
  intro equality
  cases equality

#print axioms marker_none
#print axioms marker_erased
#print axioms continuation_eq
#print axioms context_eq
#print axioms failing_callback_not_erased
end AspisR1.CuSavingsProfilingMarker
