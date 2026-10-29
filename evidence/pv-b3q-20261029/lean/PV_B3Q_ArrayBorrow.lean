import PV_B3Q_ArrayView
namespace PV_B3Q_ArrayBorrow
open Aeneas Aeneas.Std PV_B3P_Groups14227 PV_B3Q_ArrayView
set_option autoImplicit false
/-- A mutable unsizing cannot change the fixed array's length. The proof is
carried only in the model; it is not a new Rust precondition or runtime input. -/
abbrev Restorer (α : Type) (n : Usize) :=
 {back : α → Slice α // ∀ value, (back value).val.length = n.val}
def slice_borrow {α : Type} {n : Usize} (xs : Array α n) (index : Usize) :
    Result (α × Restorer α n) := do
 let old ← Slice.index_usize (source_view xs) index
 .ok (old,⟨Slice.set (source_view xs) index,by
   intro value
   have same := congrArg (fun view : Slice α => view.val.length) (restore_view xs index value)
   exact same.symm.trans (Aeneas.Std.Array.set xs index value).property⟩)
def source_mut {α : Type} {n : Usize} (xs : Array α n) (index : Usize) :
    Result (α × (α → Array α n)) := do
 let (old,back) ← slice_borrow xs index
 .ok (old,fun value => ⟨(back.val value).val,back.property value⟩)
/-- Forgetting only the length proof returns the exact pinned slice borrow port. -/
theorem slice_borrow_projection {α : Type} {n : Usize} (xs : Array α n) (index : Usize) :
    (do let (old,back) ← slice_borrow xs index; .ok (old,back.val)) =
      Slice.index_mut_usize (source_view xs) index := by
 unfold slice_borrow Slice.index_mut_usize
 cases Slice.index_usize (source_view xs) index <;> rfl
/-- The backward function is applied, then rewrapped at the original fixed
length. No returned restoration function is dropped. -/
theorem mutable_binding {α : Type} {n : Usize} (xs : Array α n) (index : Usize) :
    source_mut xs index = Array.index_mut_usize xs index := by
 unfold source_mut slice_borrow Array.index_mut_usize
 rw [←read_binding xs index]
 unfold source_read
 cases Slice.index_usize (source_view xs) index with
 | fail e => rfl
 | div => rfl
 | ok old =>
   simp only [bind_tc_ok]
   apply congrArg Result.ok
   apply congrArg (fun back : α → Array α n => (old,back))
   funext value
   rfl
/-- Concrete array IndexMut wrapper after the source's two delegation steps. -/
theorem mutable_link (α : Type) (n : Usize) : PV_B3P_Link_std_dependency_closure14
    (fun _ : Unit => Array α n → Usize → Result (α × (α → Array α n)))
    (fun _ => @source_mut α n) (fun _ => Array.index_mut_usize) := by
 intro _
 funext xs index
 exact mutable_binding xs index
#print axioms slice_borrow_projection
#print axioms mutable_binding
#print axioms mutable_link
end PV_B3Q_ArrayBorrow
