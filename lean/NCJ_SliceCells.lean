import NCJ_GuardExact
set_option autoImplicit false
noncomputable section
namespace NCJ_SliceCells
open Aeneas Aeneas.Std Result

def pick {α : Type} (s : Slice α) (i : Nat) (h : i<s.val.length) : α := s.val[i]'h

def put {α : Type} (s : Slice α) (i : Nat) (x : α) : Slice α :=
  ⟨s.val.set i x,by simpa only [List.length_set] using s.property⟩

theorem read {α : Type} (s : Slice α) (i : Usize) (h : i.val<s.val.length) :
    Slice.index_usize s i=ok (pick s i.val h) := by
  simp [Slice.index_usize,pick,h]

theorem update {α : Type} (s : Slice α) (i : Usize) (h : i.val<s.val.length) (x : α) :
    Slice.update s i x=ok (put s i.val x) := by
  simp [Slice.update,put,h]

theorem length {α : Type} (s : Slice α) (i : Nat) (x : α) :
    (put s i x).val.length=s.val.length := List.length_set

theorem frame {α : Type} (s : Slice α) (i j : Nat) (x : α) (h : j≠i) :
    (put s i x).val[j]?=s.val[j]? := by
  simp only [put,List.getElem?_set]
  split <;> simp_all

theorem selected {α : Type} (s : Slice α) (i : Nat) (x : α) (h : i<s.val.length) :
    (put s i x).val[i]?=some x := by
  simp [put,List.getElem?_set,h]

#print axioms read
#print axioms update
#print axioms length
#print axioms frame
#print axioms selected
end NCJ_SliceCells
