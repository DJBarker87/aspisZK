import PV_B3P_ClosureLinks14227
namespace PV_B3Q_Iterator4
open Aeneas Aeneas.Std PV_B3P_Groups14227 PV_B3P_Binding13227
set_option autoImplicit false
/-- Metadata for the reached non-ZST four-slot specialization. Region is an
allocation identity, never a pointer-to-integer cast. The heap is retained by
the caller; iterator methods do not read or modify the four element values. -/
structure Iter where
 region : Nat
 index : Usize
 valid : index.val ≤ 4
structure Enumerated where
 iter : Iter
 count : Usize
abbrev Slot := SlotPointer13

def source_new (region : Nat) (_cells : Four14) : Result Iter :=
 .ok ⟨region,0#usize,by scalar_tac⟩
def model_new (region : Nat) (_cells : Four14) : Result Iter :=
 .ok ⟨region,0#usize,by scalar_tac⟩

def advance (iter : Iter) (small : iter.index.val < 4) : Iter :=
 ⟨iter.region,Usize.wrapping_add iter.index 1#usize,by
   rw [cursor_increment13 iter.index small]
   omega⟩
/-- Native next caches the old pointer, compares with the end, advances self.ptr,
then returns the old slot as a unique mutable loan token. -/
def source_next (iter : Iter) : Result (Option Slot × Iter) :=
 if finish : iter.index = 4#usize then .ok (none,iter)
 else
   let small : iter.index.val < 4 := by
     have different : iter.index.val ≠ 4 := by
       intro h
       apply finish
       apply UScalar.eq_of_val_eq
       exact h
     have bound := iter.valid
     omega
   .ok (some ⟨iter.region,iter.index⟩,advance iter small)
def model_next (iter : Iter) : Result (Option Slot × Iter) :=
 if small : iter.index.val < 4 then
   .ok (some ⟨iter.region,iter.index⟩,advance iter small)
 else .ok (none,iter)

theorem next_binding (iter : Iter) : source_next iter = model_next iter := by
 unfold source_next model_next
 split
 · rename_i finish
   have stop : ¬iter.index.val < 4 := by scalar_tac
   rw [dif_neg stop]
 · rename_i not_finish
   have small : iter.index.val < 4 := by
     have bound := iter.valid
     have different : iter.index.val ≠ 4 := by
       intro h
       apply not_finish
       apply UScalar.eq_of_val_eq
       exact h
     omega
   rw [dif_pos small]

def source_enumerate_new (iter : Iter) : Result Enumerated := .ok ⟨iter,0#usize⟩
def source_enumerate_next (state : Enumerated) : Result (Option (Usize × Slot) × Enumerated) := do
 let (item,advanced) ← source_next state.iter
 match item with
 | none => .ok (none,{iter := advanced,count := state.count})
 | some slot => .ok (some (state.count,slot),
     {iter := advanced,count := Usize.wrapping_add state.count 1#usize})
def model_enumerate_next (state : Enumerated) : Result (Option (Usize × Slot) × Enumerated) := do
 let (item,advanced) ← model_next state.iter
 match item with
 | none => .ok (none,{iter := advanced,count := state.count})
 | some slot => .ok (some (state.count,slot),
     {iter := advanced,count := Usize.wrapping_add state.count 1#usize})

theorem enumerate_binding (state : Enumerated) :
    source_enumerate_next state = model_enumerate_next state := by
 unfold source_enumerate_next model_enumerate_next
 rw [next_binding]

theorem advance_region (iter : Iter) (small : iter.index.val < 4) :
    (advance iter small).region = iter.region := rfl
theorem advance_index (iter : Iter) (small : iter.index.val < 4) :
    (advance iter small).index.val = iter.index.val+1 := cursor_increment13 iter.index small

theorem end_test (iter : Iter) :
    slot_same13 ⟨iter.region,iter.index⟩ (slot_end13 iter.region) = (iter.index == 4#usize) :=
 same_region_end13 iter.region iter.index

inductive Body where | new | next | enumerate_new | enumerate_next | drop
def Signature : Body → Type
 | .new => Nat → Four14 → Result Iter
 | .next => Iter → Result (Option Slot × Iter)
 | .enumerate_new => Iter → Result Enumerated
 | .enumerate_next => Enumerated → Result (Option (Usize × Slot) × Enumerated)
 | .drop => Enumerated → Result Unit
def source : (body : Body) → Signature body
 | .new => source_new
 | .next => source_next
 | .enumerate_new => source_enumerate_new
 | .enumerate_next => source_enumerate_next
 | .drop => fun _ => .ok ()
def model : (body : Body) → Signature body
 | .new => model_new
 | .next => model_next
 | .enumerate_new => fun iter => .ok ⟨iter,0#usize⟩
 | .enumerate_next => model_enumerate_next
 | .drop => fun _ => .ok ()
/-- Body-by-body non-ZST iterator metadata binding at the actual four-QM31
caller. Memory/intrinsic realization remains V370, never a new T item. -/
theorem iterator_links : PV_B3P_Link_std_dependency_closure14 Signature source model := by
 intro body
 cases body with
 | new => rfl
 | next => funext iter; exact next_binding iter
 | enumerate_new => rfl
 | enumerate_next => funext state; exact enumerate_binding state
 | drop => rfl
#print axioms next_binding
#print axioms enumerate_binding
#print axioms advance_region
#print axioms advance_index
#print axioms end_test
#print axioms iterator_links
end PV_B3Q_Iterator4
