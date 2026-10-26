import RPz7_Hir_ProvenanceModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_Zero
open Aeneas Aeneas.Std Result Hist_Store Hir_ProvenanceModel

theorem not_initialized (data : Slice U8) (zero : Zero data) : ¬ Initialized data := by
  intro initialized
  have head := initialized.2
  simp only [Slice.index_usize,Slice.getElem?_Usize_eq] at head
  cases bytes : data.val with
  | nil => simp [bytes] at head
  | cons byte rest =>
    have first : byte = 0#u8 := zero byte (by simp [bytes])
    simp only [bytes,List.getElem?_cons_zero] at head
    simp [first] at head

#print axioms not_initialized
end AspisR1.Hir_Zero
end
