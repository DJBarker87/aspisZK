import R1Z.PV_CB_Codecs
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op71Source
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem op71_source (ops : ExternalFuns) (s : Slice U8) :
    (PV_CB_Codecs.selected ops).op71 s =
      ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes s := rfl
#print axioms op71_source
end R1Z.PV_CB_Op71Source
