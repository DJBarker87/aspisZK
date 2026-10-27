import XSd_DotSequence
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSd_MapState
/-- Generic state/error adapter: the older selected array-map implementation
and the emitted kit preserve the same final closure and first stopping result. -/
theorem source {T U F : Type} (fn : core.ops.function.FnMut F T U)
 (xs : List T) (state : F) :
 AspisV8R19.TraversalRuntime.mapState fn.call_mut xs state =
 (do let (ys,last) ← _root_.core.array.mapListFnMut fn xs state
     ok (ys.val,last)) := by
 induction xs generalizing state with
 | nil => rfl
 | cons x xs ih =>
  rw [AspisV8R19.TraversalRuntime.mapState,_root_.core.array.mapListFnMut]
  cases h : fn.call_mut state x with
  | fail e => rfl
  | div => rfl
  | ok pair =>
   rcases pair with ⟨y,next⟩
   simp [h,ih,bind_assoc_eq]
#print axioms source
end XSd_MapState
