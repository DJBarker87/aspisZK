import EmptyRootExecution
import ExtractedMaskPreparedState
import ExtractedMaskQM31Exact
import ExtractedMaskTowerAdd

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedWeightMap
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisV8R19.TraversalRuntime

abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev PreparedFor := AspisR1.ExtractedMaskPreparedState.PreparedFor
abbrev Callback := BuiltinFnMut QM Prepared
abbrev New := field.PreparedQm31Multiplier.new

private def at3 (a : Array QM 3#usize) (i : Fin 3) : QM :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)
private def prepAt3 (a : Array Prepared 3#usize) (i : Fin 3) : Prepared :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)

private def i0 : Fin 3 := ⟨0, by omega⟩
private def i1 : Fin 3 := ⟨1, by omega⟩
private def i2 : Fin 3 := ⟨2, by omega⟩

theorem prepared_map_three (x0 x1 x2 : QM)
    (h0 : Canonical x0) (h1 : Canonical x1) (h2 : Canonical x2) :
    ∃ p0 p1 p2 : Prepared,
      (core.array.Array.map Callback (Array.make 3#usize [x0,x1,x2]) New) =
        .ok (Array.make 3#usize [p0,p1,p2]) ∧
      PreparedFor p0 x0 ∧ PreparedFor p1 x1 ∧ PreparedFor p2 x2 := by
  obtain ⟨p0,hnew0,hp0⟩ := AspisR1.ExtractedMaskPreparedState.current_prepared_new x0 h0
  obtain ⟨p1,hnew1,hp1⟩ := AspisR1.ExtractedMaskPreparedState.current_prepared_new x1 h1
  obtain ⟨p2,hnew2,hp2⟩ := AspisR1.ExtractedMaskPreparedState.current_prepared_new x2 h2
  have hcall0 : Callback.call_mut New x0 = .ok (p0,New) := by
    simp [Callback, BuiltinFnMut, hnew0]
  have hcall1 : Callback.call_mut New x1 = .ok (p1,New) := by
    simp [Callback, BuiltinFnMut, hnew1]
  have hcall2 : Callback.call_mut New x2 = .ok (p2,New) := by
    simp [Callback, BuiltinFnMut, hnew2]
  have hstate : mapState Callback.call_mut [x0,x1,x2] New =
      .ok ([p0,p1,p2],New) := by
    simp [AspisV8R19.TraversalRuntime.mapState, hcall0, hcall1, hcall2]
  have hmap := Aeneas.Std.core.array.Array.map_success Callback
    (Array.make 3#usize [x0,x1,x2]) New [p0,p1,p2] New hstate
  refine ⟨p0,p1,p2,?_,hp0,hp1,hp2⟩
  simpa [Array.make] using hmap

#print axioms prepared_map_three
end AspisR1.PoseidonPreparedWeightMap
