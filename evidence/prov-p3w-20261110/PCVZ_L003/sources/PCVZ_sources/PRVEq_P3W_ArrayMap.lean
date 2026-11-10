-- PCVZ_ generic lemmas for Array.map over a literal/array with a pure callback, and indexing a mapped array.
-- Library model: core.array.Array.map is the gate's SelectorArrayMapRuntimeSlice definition (trust row HM-D: array/slice).
import Aeneas
import SelectorArrayMapRuntimeSlice
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxRecDepth 2048
namespace PRVEq_P3W

theorem mapState_pure {T U F : Type} (call : F → T → Result (U × F)) (g : T → U)
    (h : ∀ c x, call c x = ok (g x, c)) :
    ∀ (xs : List T) (c : F), AspisV8R19.TraversalRuntime.mapState call xs c = ok (xs.map g, c) := by
  intro xs
  induction xs with
  | nil => intro c; rfl
  | cons x xs ih =>
    intro c
    simp only [AspisV8R19.TraversalRuntime.mapState, h, bind_tc_ok, ih, List.map_cons]

theorem map_pure {T F U : Type} {N : Usize} (cb : core.ops.function.FnMut F T U) (g : T → U)
    (h : ∀ c x, cb.call_mut c x = ok (g x, c)) (a : Std.Array T N) (f : F) :
    core.array.Array.map cb a f
      = ok (⟨a.val.map g, by rw [List.length_map]; exact a.property⟩ : Std.Array U N) := by
  have hs := mapState_pure cb.call_mut g h a.val f
  unfold core.array.Array.map
  split
  · next ys last hm =>
    rw [hs] at hm
    simp only [Result.ok.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    rfl
  · next e hm => rw [hs] at hm; cases hm
  · next hm => rw [hs] at hm; cases hm

theorem idx_mapped_v1 {T U : Type} {N : Usize} (a : Std.Array T N) (g : T → U) (p : (a.val.map g).length = N.val)
    (k : Usize) {β : Type} (cont : U → Result β) :
    (do let x ← Std.Array.index_usize (⟨a.val.map g, p⟩ : Std.Array U N) k; cont x)
      = (do let y ← Std.Array.index_usize a k; cont (g y)) := by
  unfold Std.Array.index_usize
  have e : (⟨a.val.map g, p⟩ : Std.Array U N)[k]? = (a[k]?).map g := by
    simp [List.getElem?_map]
  rw [e]
  cases a[k]? <;> rfl

theorem idx_mapped_v2 {T U : Type} {N : Usize} (a : Std.Array T N) (g : T → U) (p : (a.val.map g).length = N.val)
    (k : Usize) {β : Type} (cont : U → Result β) :
    (do let x ← Std.Array.index_usize (⟨a.val.map g, p⟩ : Std.Array U N) k; cont x)
      = (do let y ← Std.Array.index_usize a k; cont (g y)) := by
  unfold Std.Array.index_usize
  have e : (⟨a.val.map g, p⟩ : Std.Array U N)[k]? = (a[k]?).map g := by
    show (a.val.map g)[k.val]? = (a.val[k.val]?).map g
    exact List.getElem?_map ..
  rw [e]
  cases a[k]? <;> rfl

theorem idx_mapped_v3 {T U : Type} {N : Usize} (a : Std.Array T N) (g : T → U) (p : (a.val.map g).length = N.val)
    (k : Usize) {β : Type} (cont : U → Result β) :
    (do let x ← Std.Array.index_usize (⟨a.val.map g, p⟩ : Std.Array U N) k; cont x)
      = (do let y ← Std.Array.index_usize a k; cont (g y)) := by
  unfold Std.Array.index_usize
  rcases a with ⟨l, hl⟩
  simp only [List.getElem?_map]
  sorry_probe_placeholder

end PRVEq_P3W

#print axioms PRVEq_P3W.mapState_pure
#print axioms PRVEq_P3W.map_pure
#print axioms PRVEq_P3W.idx_mapped_v1
#print axioms PRVEq_P3W.idx_mapped_v2
