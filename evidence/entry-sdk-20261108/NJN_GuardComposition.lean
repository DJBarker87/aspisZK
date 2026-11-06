import NJN_AcquireLaws
import NJN_DropLaws
import NJN_CopyLaws
set_option autoImplicit false
namespace NJN_GuardModel
/-- Restoring one overwritten entry restores the entire function, including its frame. -/
theorem replace_restore {α : Type} (f : Nat → α) (i : Nat) (v : α) :
    replace (replace f i v) i (f i) = f := by
  funext j
  by_cases eq : j = i <;> simp [replace,eq]
/-- Successful shared acquisition produces a live token at the same account cell. -/
theorem shared_live (h : Heap) (a t : Nat)
    (lo : 0 ≤ (h.cells (h.accounts a).cell).counter)
    (hi : (h.cells (h.accounts a).cell).counter < 9223372036854775807) :
    Live (acquire h a t false).1 t ⟨(h.accounts a).cell,false⟩ := by
  rw [shared_ok h a t lo hi]
  simp [Live, replace]
  omega
/-- Successful exclusive acquisition produces a live, unsplit same-cell token. -/
theorem exclusive_live (h : Heap) (a t : Nat)
    (zero : (h.cells (h.accounts a).cell).counter = 0) :
    Live (acquire h a t true).1 t ⟨(h.accounts a).cell,true⟩ := by
  rw [exclusive_ok h a t zero]
  simp [Live,replace]
/-- Library acquisition preserves admitted three/seven-account layout metadata. -/
theorem admitted_acquire (h : Heap) (a t : Nat) (ex : Bool) (adm : Admitted h) :
    Admitted (acquire h a t ex).1 := by
  rcases acquire_frame h a t 0 ex with ⟨_,hc,_⟩
  unfold Admitted at *
  rw [hc]
  exact adm
/-- Exclusive writes preserve the SAME live token and its borrow counter. -/
theorem live_write (h : Heap) (g : Guard) (t i v : Nat) (live : Live h t g) :
    Live (write h g i v) t g := by
  simpa [Live,write,replace] using live
/-- Copy's payload survives guard destruction; destruction changes no payload. -/
theorem copied_drop (h : Heap) (g : Guard) (t i v : Nat) :
    ((release (write h g i v) t g).cells g.cell).bytes i = v := by
  rw [(drop_payload (write h g i v) t g.cell g).1]
  exact write_selected h g i v
/-- Same-key aliasing does not authorize touching a different cell. -/
theorem copy_drop_frame (h : Heap) (g : Guard) (t i j v : Nat) (ne : j ≠ g.cell) :
    (release (write h g i v) t g).cells j = h.cells j := by
  rw [(drop_frame (write h g i v) t j g ne).2.2]
  exact write_cell_frame h g i j v ne
#print axioms replace_restore
#print axioms shared_live
#print axioms exclusive_live
#print axioms admitted_acquire
#print axioms live_write
#print axioms copied_drop
#print axioms copy_drop_frame
end NJN_GuardModel
