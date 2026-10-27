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
 have bridge := XSd_MapState.source fn a.val state
 cases h : _root_.core.array.mapListFnMut fn a.val state with
 | fail e => simp only [h,bind_tc_fail] at bridge; simp only [bridge,h,bind_tc_fail]
 | div => simp only [h,bind_tc_div] at bridge; simp only [bridge,h,bind_tc_div]
 | ok pair =>
  rcases pair with ⟨ys,last⟩
  simp only [h,bind_tc_ok] at bridge
  simp only [bridge,h,bind_tc_ok]
#print axioms source
end XSd_ArrayMap
