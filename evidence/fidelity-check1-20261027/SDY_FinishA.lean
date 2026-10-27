import SDY_Join_Funs
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace SDY_FinishA
open SDY_Join_Release
abbrev Q := aspis_core.field.QM31
abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut Q)
abbrev Back := Iter → Iter
abbrev State := Iter × Back
abbrev body := verifier.BatchedWeights.finish_loop.body
def old : Q := ⟨⟨99#u32,99#u32⟩,⟨99#u32,99#u32⟩⟩
def value : Q := ⟨⟨1#u32,2#u32⟩,⟨3#u32,4#u32⟩⟩
def input : Slice Q := ⟨[old],by simp⟩
def output : Slice Q := ⟨[value],by simp⟩
def state : verifier.BatchedWeights := ⟨⟨[⟨[1#u64,2#u64,3#u64,4#u64],by simp⟩],by simp⟩,0#usize⟩
def step (s : State) := body state s.1 s.2
def it (i : Nat) : Iter := ⟨⟨input,i⟩,if i=0 then 0#usize else 1#usize⟩
def restore : Back := fun r => {r with iter := {r.iter with slice := r.iter.slice.setAtNat 0 value}}
theorem value_result : verifier.BatchedWeights.value state 0#usize = ok value := by rfl
#print axioms value_result

theorem first (b : Back) : body state (it 0) b = ok (.cont (it 1,fun r => b (restore r))) := by
  unfold body verifier.BatchedWeights.finish_loop.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,input]
  rw [value_result]
  rfl
#print axioms first

theorem last (b : Back) : body state (it 1) b = ok (.done b) := by
  unfold body verifier.BatchedWeights.finish_loop.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,input]
#print axioms last

theorem run1 (b : Back) : loop step (it 1,b) = ok b := by
  rw [loop.eq_def]
  change (match body state (it 1) b with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [last]
  rfl
#print axioms run1

theorem run0 (b : Back) : loop step (it 0,b) = ok (fun r => b (restore r)) := by
  rw [loop.eq_def]
  change (match body state (it 0) b with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [first]
  exact run1 _
#print axioms run0

theorem emitted : verifier.BatchedWeights.finish state input = ok output := by
  unfold verifier.BatchedWeights.finish core.slice.Slice.iter_mut SDY_Join_enumerateRestored core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.enumerate
  simp only [bind_tc_ok]
  change (do let b ← loop step (it 0,id); ok (b (it 0)).iter.slice) = _
  rw [run0]
  rfl
#print axioms emitted
end SDY_FinishA
