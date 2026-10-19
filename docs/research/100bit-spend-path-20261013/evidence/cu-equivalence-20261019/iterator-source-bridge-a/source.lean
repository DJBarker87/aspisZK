import CuSavingsIteratorSource
import AspisR1CuRho.Finish

/-! Compare the selected emitted standard method with the concrete mutable
runtime on forward control/state and the inner iterator after writing a
returned item. Deliberately discard the backward counter: generated source
restores its captured count, which is not an observable finish result. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsIteratorBridge
open Aeneas Aeneas.Std Result
variable {T : Type}
abbrev Iter (T : Type) := Aeneas.Std.core.slice.iter.IterMut T
abbrev Enum (T : Type) := Aeneas.Std.core.iter.adapters.enumerate.Enumerate (Iter T)
abbrev SourceEnum (T : Type) := AspisR1CuIterator.Enumerate (Iter T)

def fromStd (input : Enum T) : SourceEnum T := {iter := input.iter,count := input.count}
def toStd (input : SourceEnum T) : Enum T := {iter := input.iter,count := input.count}

abbrev modelNext := @AspisR1CuRho.core.iter.adapters.enumerate.IteratorEnumerate.next
  (Iter T) T (AspisR1CuRho.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT T)

def sourceView (input : Enum T) (replacement : Usize × T) :
    Result (Option (Usize × T) × Enum T × (Enum T → Iter T)) := do
  let (value,state,back) ← CuSavingsIteratorSource.next (fromStd input)
  .ok (value,toStd state,fun out => (back (fromStd out) (some replacement)).iter)

def modelView (input : Enum T) (replacement : Usize × T) :
    Result (Option (Usize × T) × Enum T × (Enum T → Iter T)) := do
  let (value,state,back) ← modelNext input
  .ok (value,state,fun out => (back out (some replacement)).iter)

theorem source_none (input : Enum T) (replacement : Usize × T)
    (hn : Aeneas.Std.core.slice.iter.IteratorIterMut.next input.iter =
      .ok (none,input.iter,fun out _ => out)) :
    sourceView input replacement = .ok (none,input,fun out => out.iter) := by
  unfold sourceView
  rw [CuSavingsIteratorSource.source_none (fromStd input) input.iter (fun out _ => out) hn]
  rfl

theorem source_some (input : Enum T) (replacement : Usize × T) (value : T)
    (state : Iter T) (inner : Iter T → Option T → Iter T)
    (hn : Aeneas.Std.core.slice.iter.IteratorIterMut.next input.iter = .ok (some value,state,inner)) :
    sourceView input replacement = (do
      let count ← UScalar.add input.count 1#usize
      Result.ok (some (input.count,value),({iter := state,count := count} : Enum T),
        fun out : Enum T => inner out.iter (some replacement.2))) := by
  unfold sourceView
  rw [CuSavingsIteratorSource.source_some (fromStd input) value state inner hn]
  simp only [bind_assoc_eq,bind_tc_ok]
  rcases replacement with ⟨index,x⟩
  rfl

theorem model_none (input : Enum T) (replacement : Usize × T)
    (hn : Aeneas.Std.core.slice.iter.IteratorIterMut.next input.iter =
      .ok (none,input.iter,fun out _ => out)) :
    modelView input replacement = .ok (none,input,fun out => out.iter) := by
  unfold modelView modelNext AspisR1CuRho.core.iter.adapters.enumerate.IteratorEnumerate.next
  simp only [AspisR1CuRho.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    hn,bind_tc_ok]
  rfl

theorem model_some (input : Enum T) (replacement : Usize × T) (value : T)
    (state : Iter T) (inner : Iter T → Option T → Iter T)
    (hn : Aeneas.Std.core.slice.iter.IteratorIterMut.next input.iter = .ok (some value,state,inner)) :
    modelView input replacement = (do
      let count ← UScalar.add input.count 1#usize
      Result.ok (some (input.count,value),({iter := state,count := count} : Enum T),
        fun out : Enum T => inner out.iter (some replacement.2))) := by
  unfold modelView modelNext AspisR1CuRho.core.iter.adapters.enumerate.IteratorEnumerate.next
  simp only [AspisR1CuRho.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    hn,bind_tc_ok]
  change (do
    let triple ← (do
      let count ← UScalar.add input.count 1#usize
      Result.ok (some (input.count,value),({iter := state,count := count} : Enum T),
        fun (out : Enum T) (item : Option (Usize × T)) =>
          {out with iter := inner out.iter (item.map Prod.snd)}))
    Result.ok (triple.1,triple.2.1,fun out : Enum T => (triple.2.2 out (some replacement)).iter)) = _
  simp only [bind_assoc_eq,bind_tc_ok]
  rfl

theorem source_model_write_eq (input : Enum T) (replacement : Usize × T) :
    sourceView input replacement = modelView input replacement := by
  have hlen : input.iter.slice.len.val = input.iter.slice.val.length := by
    simpa only [Slice.length] using Slice.len_val input.iter.slice
  by_cases hi : input.iter.i < input.iter.slice.val.length
  · let state : Iter T := {input.iter with i := input.iter.i+1}
    let inner : Iter T → Option T → Iter T := fun out value => match value with
      | none => out
      | some x => {out with slice := out.slice.setAtNat input.iter.i x}
    have hn : Aeneas.Std.core.slice.iter.IteratorIterMut.next input.iter =
        .ok (some (input.iter.slice.val[input.iter.i]'hi),state,inner) := by
      unfold Aeneas.Std.core.slice.iter.IteratorIterMut.next
      split
      · apply congrArg Result.ok
        apply Prod.ext
        · apply congrArg some
          exact Slice.getElem_Nat_eq input.iter.slice input.iter.i hi
        · apply Prod.ext
          · rfl
          · funext out value
            cases value <;> rfl
      · rename_i hbad;exact False.elim (hbad (by rw [hlen];exact hi))
    rw [source_some input replacement _ state inner hn,model_some input replacement _ state inner hn]
  · have hn : Aeneas.Std.core.slice.iter.IteratorIterMut.next input.iter =
        .ok (none,input.iter,fun out _ => out) := by
      unfold Aeneas.Std.core.slice.iter.IteratorIterMut.next
      split
      · rename_i hbad;exact False.elim (hi (by rw [←hlen];exact hbad))
      · rfl
    rw [source_none input replacement hn,model_none input replacement hn]

#print axioms source_none
#print axioms source_some
#print axioms model_none
#print axioms model_some
#print axioms source_model_write_eq
end AspisR1.CuSavingsIteratorBridge
