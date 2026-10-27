import R1Z.PV_CB_Codecs
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op72Source
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem op72_source (ops : ExternalFuns) (x : aspis_core.field.QM31) (s : Slice U8) :
    (PV_CB_Codecs.selected ops).op72 x s =
      ProverRwDictionaryBytesSource.aspis_core.field.QM31.write_le_bytes x s := rfl
#print axioms op72_source
end R1Z.PV_CB_Op72Source
