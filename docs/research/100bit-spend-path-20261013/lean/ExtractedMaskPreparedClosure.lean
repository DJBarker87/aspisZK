import ExtractedMaskPreparedState
set_option autoImplicit false
namespace AspisR1.ExtractedMaskPreparedClosure
open Aeneas.Std Result
open AspisR1SelectedMaskProbe
open ExtractedMaskPreparedState

theorem call_eq (left : Component) (right : CM) :
    field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
      () (left, right) = (do
        let a ← Array.index_usize left 0#usize
        let m0 ← field.M31.mul a right.a
        let b ← Array.index_usize left 1#usize
        let m1 ← field.M31.mul b right.b
        let s ← Array.index_usize left 2#usize
        let t ← field.M31.add right.a right.b
        let m2 ← field.M31.mul s t
        let low ← field.M31.sub m0 m1
        let high0 ← field.M31.sub m2 m0
        let high ← field.M31.sub high0 m1
        ok ({ a := low, b := high } : CM)) := by rfl

#print axioms call_eq
end AspisR1.ExtractedMaskPreparedClosure
