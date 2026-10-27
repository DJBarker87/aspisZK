import XSd_MapState
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSd_ArrayMap
/-- Full array Result association at every length, callback and initial state.
The dependent length proofs erase by proof irrelevance; closure evaluation is
identical by the generic state adapter. -/
theorem source {T U F : Type} {N : Usize} (fn : core.ops.function.FnMut F T U)
 (a : Array T N) (state : F) :
 Aeneas.Std.core.array.Array.map fn a state = _root_.core.array.Array.map fn a state := by
 unfold Aeneas.Std.core.array.Array.map _root_.core.array.Array.map
 rw [XSd_MapState.source]
 cases h : _root_.core.array.mapListFnMut fn a.val state with
 | fail e => rfl
 | div => rfl
 | ok pair => rcases pair with ⟨ys,last⟩; rfl
#print axioms source
end XSd_ArrayMap
