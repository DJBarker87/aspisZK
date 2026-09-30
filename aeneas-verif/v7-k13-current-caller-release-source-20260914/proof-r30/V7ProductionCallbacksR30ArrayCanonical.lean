import V7ProductionCallbacksR30MutableCanonical

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ProductionCallbacksR30ArrayCanonical
open V7ProductionCallbacksR30MutableCanonical

theorem array_index_all {T : Type} [Inhabited T] {N : Std.Usize}
    (P : T → Prop) (values : Array T N) (index : Std.Usize) (output : T)
    (canonical : SliceAll P values.to_slice)
    (run : Array.index_usize values index = ok output) : P output := by
  unfold Array.index_usize at run
  split at run
  · cases run
  · rename_i present
    have listPresent : values.val[index.val]? = some output := by
      simpa [Result.ok.inj run] using present
    have bound : index.val < values.val.length := by
      by_contra absent
      have none := List.getElem?_eq_none (l := values.val) (i := index.val) (by omega)
      rw [none] at listPresent
      cases listPresent
    have exactOutput := List.getElem!_of_getElem? listPresent
    rw [← exactOutput]
    exact canonical index.val bound

theorem array_update_all {T : Type} [Inhabited T] {N : Std.Usize}
    (P : T → Prop) (before after : Array T N) (index : Std.Usize) (value : T)
    (canonical : SliceAll P before.to_slice) (valueCanonical : P value)
    (run : Array.update before index value = ok after) : SliceAll P after.to_slice := by
  unfold Array.update at run
  split at run
  · cases run
  · cases run
    exact slice_set_all P before.to_slice index.val value canonical valueCanonical

#print axioms array_index_all
#print axioms array_update_all
end V7ProductionCallbacksR30ArrayCanonical
