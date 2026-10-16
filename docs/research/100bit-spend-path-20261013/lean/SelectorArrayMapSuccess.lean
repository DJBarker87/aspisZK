import SelectorArrayMapRuntimeSlice

/-! Focused success rule for the dependent match in the extracted array map.
The successful discriminant is identified by Result injection before the
length-certificate proof is compared. -/
set_option autoImplicit false
namespace Aeneas.Std
open Aeneas Aeneas.Std Result AspisV8R19.TraversalRuntime

theorem core.array.Array.map_success
    {T U F : Type} {N : Usize}
    (callback : core.ops.function.FnMut F T U) (self : Array T N) (f : F)
    (ys : List U) (last : F)
    (hstate : mapState callback.call_mut self.val f = .ok (ys, last)) :
    core.array.Array.map callback self f =
      .ok ⟨ys, (mapState_length _ _ _ _ _ hstate).trans self.property⟩ := by
  unfold core.array.Array.map
  split
  · rename_i ys' last' heq
    have hpair : (ys', last') = (ys, last) := Result.ok.inj (heq.symm.trans hstate)
    cases hpair
    rfl
  · rename_i error heq
    have hbad : Result.fail error = Result.ok (ys, last) := heq.symm.trans hstate
    cases hbad
  · rename_i heq
    have hbad : Result.div = Result.ok (ys, last) := heq.symm.trans hstate
    cases hbad

#print axioms core.array.Array.map_success

end Aeneas.Std
