import R1Z.PV_Ext_IndexCompressFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Ext_IndexBridge
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Complete Result equality for the unadopted candidate index leaf. This is
    not an extraction or source theorem for the shipped slice iterator. -/
theorem reference :
    PV_Ext_IndexCompress.compress_tagged_tuple =
      @ProverRwP6CompressSource.compress _ _ := rfl

theorem loop_reference :
    PV_Ext_IndexCompress.compress_tagged_tuple_loop =
      @ProverRwP6CompressSource.compress_loop _ _ := rfl

theorem body_reference :
    PV_Ext_IndexCompress.compress_tagged_tuple_loop.body =
      @ProverRwP6CompressSource.compress_loop.body _ _ := rfl

#print axioms reference
#print axioms loop_reference
#print axioms body_reference
end R1Z.PV_Ext_IndexBridge
