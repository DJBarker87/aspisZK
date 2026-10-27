import RPv_FIy_EmptyRootShape
import RPv_FIy_ArraySlot
set_option autoImplicit false
namespace AspisR1.FIy_EmptyRootMap
open Aeneas Aeneas.Std Result FIq_Native

theorem list_value (xs : List U32) :
    AspisV8R19.TraversalRuntime.mapState (BuiltinFnMut U32 U32).call_mut xs field.M31_constructor=
      ok (xs,field.M31_constructor) := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [AspisV8R19.TraversalRuntime.mapState,BuiltinFnMut,field.M31_constructor,bind_tc_ok]
    change (do let p ← AspisV8R19.TraversalRuntime.mapState (BuiltinFnMut U32 U32).call_mut xs field.M31_constructor
               ok (x::p.1,p.2))=ok (x::xs,field.M31_constructor)
    rw [ih]
    rfl

theorem value {N : Usize} (a : Array U32 N) :
    FIq_Native.core.array.Array.map (BuiltinFnMut U32 U32) a field.M31_constructor=ok a := by
  unfold FIq_Native.core.array.Array.map Aeneas.Std.core.array.Array.map
  split
  · rename_i ys last h
    have eq := Prod.mk.inj (Result.ok.inj ((list_value a.val).symm.trans h))
    apply congrArg Result.ok
    apply Subtype.ext
    exact eq.1.symm
  · rename_i e h
    rw [list_value] at h
    cases h
  · rename_i h
    rw [list_value] at h
    cases h

#print axioms list_value
#print axioms value
end AspisR1.FIy_EmptyRootMap
