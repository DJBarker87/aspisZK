-- PCVZ_ generic lemmas: Array.map over a 4-element literal array with an effectful callback whose state is constant.
-- Library model: core.array.Array.map is the gate's SelectorArrayMapRuntimeSlice definition (trust row HM-D: array/slice).
import Aeneas
import SelectorArrayMapRuntimeSlice
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxRecDepth 2048
namespace PRVEq_P3W

theorem arr4 {T : Type} (a : Std.Array T 4#usize) :
    ∃ x0 x1 x2 x3, a = Std.Array.make 4#usize [x0, x1, x2, x3] := by
  obtain ⟨l, hl⟩ := a
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, l⟩⟩⟩⟩⟩
  · simp at hl
  · simp at hl
  · simp at hl
  · simp at hl
  · exact ⟨x0, x1, x2, x3, rfl⟩
  · simp at hl

theorem map_ok {T F U : Type} {N : Usize} (cb : core.ops.function.FnMut F T U) (a : Std.Array T N) (f : F)
    (ys : List U) (last : F) (hs : AspisV8R19.TraversalRuntime.mapState cb.call_mut a.val f = ok (ys, last)) :
    core.array.Array.map cb a f
      = ok (⟨ys, (AspisV8R19.TraversalRuntime.mapState_length _ _ _ _ _ hs).trans a.property⟩ : Std.Array U N) := by
  unfold core.array.Array.map
  split
  · next ys' last' hm =>
    rw [hs] at hm
    simp only [Result.ok.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    rfl
  · next e hm => rw [hs] at hm; cases hm
  · next hm => rw [hs] at hm; cases hm

theorem map_fail {T F U : Type} {N : Usize} (cb : core.ops.function.FnMut F T U) (a : Std.Array T N) (f : F)
    (e : Error) (hs : AspisV8R19.TraversalRuntime.mapState cb.call_mut a.val f = fail e) :
    core.array.Array.map cb a f = fail e := by
  unfold core.array.Array.map
  split
  · next ys' last' hm => rw [hs] at hm; cases hm
  · next e' hm =>
    rw [hs] at hm
    simp only [Result.fail.injEq] at hm
    rw [hm]
  · next hm => rw [hs] at hm; cases hm

theorem map_div {T F U : Type} {N : Usize} (cb : core.ops.function.FnMut F T U) (a : Std.Array T N) (f : F)
    (hs : AspisV8R19.TraversalRuntime.mapState cb.call_mut a.val f = div) :
    core.array.Array.map cb a f = div := by
  unfold core.array.Array.map
  split
  · next ys' last' hm => rw [hs] at hm; cases hm
  · next e' hm => rw [hs] at hm; cases hm
  · next hm => rfl

theorem map4_mon {T F U β : Type} (cb : core.ops.function.FnMut F T U) (R : T → Result U) (f : F)
    (hcb : ∀ x, cb.call_mut f x = (do let y ← R x; ok (y, f)))
    (x0 x1 x2 x3 : T) (cont : Std.Array U 4#usize → Result β) :
    (do let a ← core.array.Array.map cb (Std.Array.make 4#usize [x0, x1, x2, x3]) f; cont a)
      = (do let y0 ← R x0; let y1 ← R x1; let y2 ← R x2; let y3 ← R x3
            cont (Std.Array.make 4#usize [y0, y1, y2, y3])) := by
  rcases h0 : R x0 with y0 | e0 | _
  · rcases h1 : R x1 with y1 | e1 | _
    · rcases h2 : R x2 with y2 | e2 | _
      · rcases h3 : R x3 with y3 | e3 | _
        · have hs : AspisV8R19.TraversalRuntime.mapState cb.call_mut [x0, x1, x2, x3] f
              = ok ([y0, y1, y2, y3], f) := by
            simp [AspisV8R19.TraversalRuntime.mapState, hcb, h0, h1, h2, h3]
          rw [map_ok cb (Std.Array.make 4#usize [x0, x1, x2, x3]) f _ _ hs]
          simp [h0, h1, h2, h3]
          rfl
        · have hs : AspisV8R19.TraversalRuntime.mapState cb.call_mut [x0, x1, x2, x3] f = fail e3 := by
            simp [AspisV8R19.TraversalRuntime.mapState, hcb, h0, h1, h2, h3]
          rw [map_fail cb (Std.Array.make 4#usize [x0, x1, x2, x3]) f _ hs]
          simp [h0, h1, h2, h3]
        · have hs : AspisV8R19.TraversalRuntime.mapState cb.call_mut [x0, x1, x2, x3] f = div := by
            simp [AspisV8R19.TraversalRuntime.mapState, hcb, h0, h1, h2, h3]
          rw [map_div cb (Std.Array.make 4#usize [x0, x1, x2, x3]) f hs]
          simp [h0, h1, h2, h3]
      · have hs : AspisV8R19.TraversalRuntime.mapState cb.call_mut [x0, x1, x2, x3] f = fail e2 := by
          simp [AspisV8R19.TraversalRuntime.mapState, hcb, h0, h1, h2]
        rw [map_fail cb (Std.Array.make 4#usize [x0, x1, x2, x3]) f _ hs]
        simp [h0, h1, h2]
      · have hs : AspisV8R19.TraversalRuntime.mapState cb.call_mut [x0, x1, x2, x3] f = div := by
          simp [AspisV8R19.TraversalRuntime.mapState, hcb, h0, h1, h2]
        rw [map_div cb (Std.Array.make 4#usize [x0, x1, x2, x3]) f hs]
        simp [h0, h1, h2]
    · have hs : AspisV8R19.TraversalRuntime.mapState cb.call_mut [x0, x1, x2, x3] f = fail e1 := by
        simp [AspisV8R19.TraversalRuntime.mapState, hcb, h0, h1]
      rw [map_fail cb (Std.Array.make 4#usize [x0, x1, x2, x3]) f _ hs]
      simp [h0, h1]
    · have hs : AspisV8R19.TraversalRuntime.mapState cb.call_mut [x0, x1, x2, x3] f = div := by
        simp [AspisV8R19.TraversalRuntime.mapState, hcb, h0, h1]
      rw [map_div cb (Std.Array.make 4#usize [x0, x1, x2, x3]) f hs]
      simp [h0, h1]
  · have hs : AspisV8R19.TraversalRuntime.mapState cb.call_mut [x0, x1, x2, x3] f = fail e0 := by
      simp [AspisV8R19.TraversalRuntime.mapState, hcb, h0]
    rw [map_fail cb (Std.Array.make 4#usize [x0, x1, x2, x3]) f _ hs]
    simp [h0]
  · have hs : AspisV8R19.TraversalRuntime.mapState cb.call_mut [x0, x1, x2, x3] f = div := by
      simp [AspisV8R19.TraversalRuntime.mapState, hcb, h0]
    rw [map_div cb (Std.Array.make 4#usize [x0, x1, x2, x3]) f hs]
    simp [h0]

end PRVEq_P3W

#print axioms PRVEq_P3W.arr4
#print axioms PRVEq_P3W.map_ok
#print axioms PRVEq_P3W.map_fail
#print axioms PRVEq_P3W.map_div
#print axioms PRVEq_P3W.map4_mon
#print BuiltinFnMut
