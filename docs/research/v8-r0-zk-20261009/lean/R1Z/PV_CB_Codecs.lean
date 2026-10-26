import R1Z.PV_CB_VecArray
import R1Z.ProverRwP6FlatSource
import R1Z.ProverRwSuccessParser
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Codecs
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- Retain source bounds checks, short-input failure and sequential slice writes. -/
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {PV_CB_VecArray.selected ops with
    op51 := ProverRwP6FlatSource.wide_bytes_flat
    op71 := ProverRwSuccessParser.parse
    op72 := ProverRwDictionaryBytes.Src.write}
theorem op51_installed (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (selected ops).op51 x = ProverRwP6FlatSource.wide_bytes_flat x := rfl
theorem op71_installed (ops : ExternalFuns) (s : Slice U8) :
    (selected ops).op71 s =
      ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes s := rfl
theorem op72_installed (ops : ExternalFuns) (x : aspis_core.field.QM31) (s : Slice U8) :
    (selected ops).op72 x s =
      ProverRwDictionaryBytesSource.aspis_core.field.QM31.write_le_bytes x s := rfl
#print axioms op51_installed
#print axioms op71_installed
#print axioms op72_installed
end R1Z.PV_CB_Codecs
