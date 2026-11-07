import PCD_ArrayExt
set_option autoImplicit false
namespace PCD_Observe
open Aeneas.Std PCD_LaneRef
inductive Slot where
  | master (i : Fin 32)
  | bump
  | laneId
  | nextIndex
  | root (word : Fin 8)
  | frontier (level : Fin 20) (word : Fin 8)

def value (lane : Lane) : Slot → Nat
  | .master i => (lane.master.val[i.val]'(by rw [lane.master.property]; exact i.isLt)).val
  | .bump => lane.bump.val
  | .laneId => lane.lane_id.val
  | .nextIndex => lane.tree.next_leaf_index.val
  | .root w => (lane.tree.root.val[w.val]'(by rw [lane.tree.root.property]; exact w.isLt)).val
  | .frontier l w =>
    let node := lane.tree.frontier.val[l.val]'(by rw [lane.tree.frontier.property]; exact l.isLt)
    (node.val[w.val]'(by rw [node.property]; exact w.isLt)).val

/-- Composition of ONE arbitrary native scalar observation into full typed
value equality. Padding is outside the Rust value relation; every value field
is included. This auxiliary lemma is not a row root with an endpoint premise. -/
theorem extensionality (x y : Lane) (same : ∀ s, value x s = value y s) : x = y := by
  have master : x.master = y.master := PCD_ArrayExt.array_ext _ _
    (fun i => by simpa [value] using same (.master i))
  have bump : x.bump = y.bump := PCD_ArrayExt.scalar_ext _ _ (by simpa [value] using same .bump)
  have laneId : x.lane_id = y.lane_id := PCD_ArrayExt.scalar_ext _ _ (by simpa [value] using same .laneId)
  have next : x.tree.next_leaf_index = y.tree.next_leaf_index :=
    PCD_ArrayExt.scalar_ext _ _ (by simpa [value] using same .nextIndex)
  have root : x.tree.root = y.tree.root := PCD_ArrayExt.array_ext _ _
    (fun i => by simpa [value] using same (.root i))
  have frontier : x.tree.frontier = y.tree.frontier := by
    apply Subtype.ext
    apply List.ext_getElem
    · exact x.tree.frontier.property.trans y.tree.frontier.property.symm
    · intro i hx hy
      apply PCD_ArrayExt.array_ext
      intro w
      exact same (.frontier ⟨i, by have len : x.tree.frontier.val.length = 20 := x.tree.frontier.property; omega⟩ w)
  cases x with
  | mk xm xb xl xt =>
    cases y with
    | mk ym yb yl yt =>
      cases master
      cases bump
      cases laneId
      cases xt with
      | mk xn xr xf =>
        cases yt with
        | mk yn yr yf =>
          cases next
          cases root
          cases frontier
          rfl
#print axioms extensionality
end PCD_Observe
