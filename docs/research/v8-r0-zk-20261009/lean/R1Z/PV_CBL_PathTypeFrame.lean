import R1Z.PV_CBL_PathTypes
namespace R1Z.PV_CBL_PathTypeFrame
open ProverRwFull
set_option autoImplicit false

/-- Path representation does not alter the frozen digest carriers. -/
theorem sha_core_unchanged (base : ExternalTypes) :
    (PV_CBL_PathTypes.selectedTypes base).op10 = base.op10 := rfl

theorem generic_array_unchanged (base : ExternalTypes) :
    (PV_CBL_PathTypes.selectedTypes base).op11 = base.op11 := rfl

theorem block_buffer_unchanged (base : ExternalTypes) :
    (PV_CBL_PathTypes.selectedTypes base).op14 = base.op14 := rfl

theorem core_wrapper_unchanged (base : ExternalTypes) :
    (PV_CBL_PathTypes.selectedTypes base).op15 = base.op15 := rfl

theorem variable_wrapper_unchanged (base : ExternalTypes) :
    (PV_CBL_PathTypes.selectedTypes base).op16 = base.op16 := rfl

#print axioms sha_core_unchanged
#print axioms generic_array_unchanged
#print axioms block_buffer_unchanged
#print axioms core_wrapper_unchanged
#print axioms variable_wrapper_unchanged
end R1Z.PV_CBL_PathTypeFrame
