import PSem_Slices
set_option autoImplicit false
namespace AspisR1.PSem_Lenses
open Aeneas Aeneas.Std Result

theorem take_setSlice {T : Type} (b replacement : List T) (start : Nat)
    (fits : start+replacement.length ≤ b.length) :
    (b.setSlice! start replacement).take (start+replacement.length)=
      b.take start ++ replacement := by
  have firstLength : (b.take start).length=start := by
    rw [List.length_take,Nat.min_eq_left (by omega)]
  have joinedLength : (b.take start ++ replacement).length=start+replacement.length := by
    rw [List.length_append,firstLength]
  simp only [List.setSlice!,Nat.min_eq_left (show replacement.length ≤ b.length-start by omega),
    List.take_length]
  rw [List.take_append,joinedLength,Nat.sub_self,List.take_zero,List.append_nil,
    ←joinedLength,List.take_length]

theorem range_write {T : Type} (input window : Slice T) (back : Slice T → Slice T)
    (start stop : Usize)
    (h : core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice T)
      input {start:=start,«end»:=stop}=ok (window,back)) (replacement : Slice T) :
    (back replacement).val=input.val.setSlice! start.val replacement.val := by
  simp only [Slice.index_mut_SliceIndexRangeUsizeSliceInst] at h
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index_mut at h
  split at h
  · have lens := congrArg Prod.snd (Result.ok.inj h)
    exact (congrArg (fun f : Slice T → Slice T => (f replacement).val) lens).symm
  · cases h

theorem range_prefix {T : Type} (input window : Slice T) (back : Slice T → Slice T)
    (start stop : Usize)
    (h : core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice T)
      input {start:=start,«end»:=stop}=ok (window,back)) (replacement : Slice T)
    (length : replacement.val.length=stop.val-start.val) :
    (back replacement).val.take stop.val=input.val.take start.val ++ replacement.val := by
  have bounds : start.val ≤ stop.val ∧ stop.val ≤ input.val.length := by
    simp only [Slice.index_mut_SliceIndexRangeUsizeSliceInst] at h
    unfold core.slice.index.SliceIndexRangeUsizeSlice.index_mut at h
    split at h
    · assumption
    · cases h
  rw [range_write input window back start stop h replacement]
  have finish : stop.val=start.val+replacement.val.length := by omega
  rw [finish]
  exact take_setSlice input.val replacement.val start.val (by omega)

#print axioms take_setSlice
#print axioms range_write
#print axioms range_prefix
end AspisR1.PSem_Lenses
