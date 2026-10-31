import PV_B3P_ClosureLinks14227
namespace PV_B3Q_ForwardPointer
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
/-- Logical projection of the non-ZST Iter fields in deployed source: pointer
position, end position, and their one shared backing region. Actual byte-pointer
operations/load semantics remain V370. No address is observed by the caller. -/
structure Cursor (α : Type) where
 cells : Slice α
 position : Nat
 bound : position ≤ cells.val.length

def native_new {α : Type} (cells : Slice α) : Cursor α := ⟨cells,0,Nat.zero_le _⟩
def view {α : Type} (c : Cursor α) : core.slice.iter.Iter α := ⟨c.cells,c.position⟩
/-- The source tests pointer==end, returns old pointer on success, and increments
only the stored pointer. Constructor/invariant identify this with index<length. -/
def native_next {α : Type} (c : Cursor α) : Result (Option α × Cursor α) :=
 if h : c.position = c.cells.val.length then
  .ok (none,c)
 else
  let small : c.position < c.cells.val.length := by have b := c.bound; omega
  .ok (some c.cells.val[c.position],⟨c.cells,c.position+1,by omega⟩)

theorem constructor_binding {α : Type} (cells : Slice α) :
 Result.ok (view (native_new cells)) = core.slice.Slice.iter cells := rfl

theorem next_binding {α : Type} (c : Cursor α) :
 (do let (item,next) ← native_next c; .ok (item,view next)) =
 core.slice.iter.IteratorSliceIter.next (view c) := by
 unfold native_next core.slice.iter.IteratorSliceIter.next view
 by_cases end_ : c.position = c.cells.val.length
 · have h : ¬c.position < c.cells.len := by
     change ¬c.position < c.cells.val.length
     omega
   simp only [end_,dif_pos,h,dif_neg,bind_tc_ok]
 · have h : c.position < c.cells.len := by
     change c.position < c.cells.val.length
     have b := c.bound
     omega
   simp only [end_,dif_neg,h,dif_pos,bind_tc_ok]
   rfl

theorem next_preserves_region {α : Type} (c : Cursor α) :
 ∃ item next, native_next c = .ok (item,next) ∧ next.cells = c.cells ∧
   (item = none → next.position = c.position) ∧
   (item ≠ none → next.position = c.position+1) := by
 unfold native_next
 split
 · exact ⟨none,c,rfl,rfl,fun _ => rfl,fun h => False.elim (h rfl)⟩
 · refine ⟨_,_,rfl,rfl,?_,fun _ => rfl⟩
   intro impossible
   cases impossible

/-- Actual model signature, with source state invariant retained in the
interpretation. The domain is precisely the constructor-reachable cursors. -/
theorem iterator_link (α : Type) : PV_B3P_Link_std_dependency_closure14
 (fun _ : Unit => Cursor α → Result (Option α × core.slice.iter.Iter α))
 (fun _ c => do let (item,next) ← native_next c; .ok (item,view next))
 (fun _ c => core.slice.iter.IteratorSliceIter.next (view c)) := by
 intro _
 funext c
 exact next_binding c
#print axioms constructor_binding
#print axioms next_binding
#print axioms next_preserves_region
#print axioms iterator_link
end PV_B3Q_ForwardPointer
