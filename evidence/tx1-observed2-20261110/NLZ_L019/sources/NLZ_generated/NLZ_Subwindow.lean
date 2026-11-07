import NLZ_FrameChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLZ_Resources
open Aeneas Aeneas.Std
/-- Same-allocation subwindow. This operation never creates another owner. -/
def subwindow (w : Window) (offset length : Nat) : Window :=
 ⟨w.allocation,w.offset+offset,length⟩
/-- Symbolic slice algebra only; no large concrete buffer reduction. -/
theorem slice_nested {α : Type} (bytes : List α) (base size offset length : Nat)
 (inside : offset+length≤size) :
 (((bytes.drop base).take size).drop offset).take length =
 (bytes.drop (base+offset)).take length := by
 rw [List.drop_take,List.take_take,List.drop_drop]
 have bound : length≤size-offset := by omega
 rw [Nat.min_eq_left bound]
/-- Full byte AND initialization relation for a physical subwindow. Pointer
identity alone is deliberately insufficient for this lemma. -/
theorem subview (h : Heap) (w : Window) (bytes : List U8) (offset length : Nat)
 (view : View h w bytes) (inside : offset+length≤w.length) :
 View h (subwindow w offset length) ((bytes.drop offset).take length) := by
 obtain ⟨o,found,bound,width,content,initialized⟩ := view
 refine ⟨o,found,?_,?_,?_,?_⟩
 · change w.offset+offset+length≤o.bytes.length
   omega
 · rw [List.length_take,List.length_drop,width]
   exact Nat.min_eq_left (by omega)
 · change (o.bytes.drop (w.offset+offset)).take length = _
   rw [←content]
   exact (slice_nested o.bytes w.offset w.length offset length inside).symm
 · change (o.initialized.drop (w.offset+offset)).take length = _
   rw [←slice_nested o.initialized w.offset w.length offset length inside,initialized]
   simp only [List.drop_replicate,List.take_replicate]
   rw [Nat.min_eq_left (by omega)]
   rfl
#print axioms slice_nested
#print axioms subview
end AspisR1.NLZ_Resources
end
