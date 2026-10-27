import JGx_EntryReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_EntryIndices
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers

theorem proof (entry : Entry) : Slice.index_usize (entry.second secondSizes) 0#usize=
    ok (entry.snapshot 0 58295 58295) := rfl
#print axioms proof

theorem checkpoint (entry : Entry) : Slice.index_usize (entry.second secondSizes) 6#usize=
    ok (entry.snapshot 6 1768 1768) := rfl
#print axioms checkpoint
end AspisR1.JGx_EntryIndices
end
