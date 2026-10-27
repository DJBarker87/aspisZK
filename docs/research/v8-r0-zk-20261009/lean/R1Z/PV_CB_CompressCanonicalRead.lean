import R1Z.PV_CB_CompressCanonicalContext
set_option autoImplicit false
namespace R1Z.PV_CB_CompressCanonicalRead
open Aeneas Aeneas.Std Result

def Valid (values : Slice U32) : Prop := ∀ value ∈ values.val, PV_CB_CanonicalM31.Valid value

theorem read (values : Slice U32) (valid : Valid values) (i : Usize)
    (bound : i.val < (Slice.len values).val) :
    ∃ value, Slice.index_usize values i = ok value ∧ PV_CB_CanonicalM31.Valid value := by
  have inside : i.val < values.val.length := bound
  obtain ⟨value,hvalue,helement⟩ := WP.spec_imp_exists (Slice.index_usize_spec values i inside)
  refine ⟨value,hvalue,?_⟩
  rw [helement]
  exact valid _ (List.getElem_mem inside)
#print axioms read
end R1Z.PV_CB_CompressCanonicalRead
