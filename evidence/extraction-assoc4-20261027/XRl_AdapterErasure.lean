import XRl_Adapter
open Aeneas Aeneas.Std Result
namespace XRl_Adapter
/-- Erasure is only a Result/value projection, not a mutation-state law. -/
def eraseRestoration {T : Type} :
    Result (Option T × core.slice.iter.IterMut T ×
      (core.slice.iter.IterMut T → Option T → core.slice.iter.IterMut T)) →
    Result (Option T × core.slice.iter.IterMut T)
  | .ok (v,s,_) => .ok (v,s)
  | .fail e => .fail e
  | .div => .div

theorem next_projection {T : Type} (s : core.slice.iter.IterMut T) :
    XRk_next s = eraseRestoration (core.slice.iter.IteratorIterMut.next s) := by
  unfold XRk_next
  cases core.slice.iter.IteratorIterMut.next s with
  | fail e => rfl
  | div => rfl
  | ok r => rcases r with ⟨v,s,back⟩; rfl

theorem next_back_projection {T : Type} (s : core.slice.iter.IterMut T) :
    XRk_nextBackPair s = eraseRestoration
      (core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back s) := by
  unfold XRk_nextBackPair
  cases core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back s with
  | fail e => rfl
  | div => rfl
  | ok r => rcases r with ⟨v,s,back⟩; rfl

def forwardInitial : core.slice.iter.IterMut Bool := ⟨⟨[false],by scalar_tac⟩,0⟩
def borrowedMutation : Result (core.slice.iter.IterMut Bool) := do
  let (_,s,back) ← core.slice.iter.IteratorIterMut.next forwardInitial
  ok (back s (some true))
def droppedMutation : Result (core.slice.iter.IterMut Bool) := do
  let (_,s) ← XRk_next forwardInitial
  ok s

theorem restoration_not_erasable : borrowedMutation ≠ droppedMutation := by
  intro h
  have hs := congrArg (fun r => match r with
    | .ok s => s.slice.val
    | _ => []) h
  change [true] = [false] at hs
  cases hs

#print axioms next_projection
#print axioms next_back_projection
#print axioms restoration_not_erasable
end XRl_Adapter
