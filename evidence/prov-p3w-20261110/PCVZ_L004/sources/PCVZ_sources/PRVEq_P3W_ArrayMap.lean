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

def mapArr {T U : Type} {N : Usize} (g : T → U) (a : Std.Array T N) : Std.Array U N :=
  ⟨a.val.map g, by rw [List.length_map]; exact a.property⟩

theorem map_pure {T F U : Type} {N : Usize} (cb : core.ops.function.FnMut F T U) (g : T → U)
    (h : ∀ c x, cb.call_mut c x = ok (g x, c)) (a : Std.Array T N) (f : F) :
    core.array.Array.map cb a f = ok (mapArr g a) := by
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

theorem getElem?_mapArr {T U : Type} {N : Usize} (g : T → U) (a : Std.Array T N) (k : Usize) :
    (mapArr g a)[k]? = (a[k]?).map g := by
  first
  | simp [mapArr, List.getElem?_map]
  | (unfold mapArr; simp [List.getElem?_map])
  | (show (a.val.map g)[k.val]? = (a.val[k.val]?).map g; exact List.getElem?_map ..)

theorem idx_mapArr {T U : Type} {N : Usize} (g : T → U) (a : Std.Array T N)
    (k : Usize) {β : Type} (cont : U → Result β) :
    (do let x ← Std.Array.index_usize (mapArr g a) k; cont x)
      = (do let y ← Std.Array.index_usize a k; cont (g y)) := by
  unfold Std.Array.index_usize
  rw [getElem?_mapArr]
  cases a[k]? <;> rfl

end PRVEq_P3W

#print axioms PRVEq_P3W.mapState_pure
#print axioms PRVEq_P3W.map_pure
#print axioms PRVEq_P3W.getElem?_mapArr
#print axioms PRVEq_P3W.idx_mapArr
