import R1Z.ProverRwP6BodyData
import R1Z.PV_CB_Op71Source
import R1Z.PV_CB_Op72Source
import R1Z.PV_CB_Op80Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Codecs
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev selected := ProverRwP6BodyStore.selected
theorem op71_source (ops : ExternalFuns) (s : Slice U8) :
    (selected ops).op71 s =
      ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes s := by
  exact PV_CB_Op71Source.op71_source ops s
#print axioms op71_source
theorem op72_source (ops : ExternalFuns) (x : aspis_core.field.QM31) (s : Slice U8) :
    (selected ops).op72 x s =
      ProverRwDictionaryBytesSource.aspis_core.field.QM31.write_le_bytes x s := by
  exact PV_CB_Op72Source.op72_source ops x s
#print axioms op72_source
theorem op80_source (ops : ExternalFuns) {E : Type}
    (inst : aspis_core.r0.scalar.CodeField E) (x y : E) (h : Array E 4#usize) :
    (selected ops).op80 inst x y h =
      ProverRwSuccessPhiSource.generic54.phi_inverse inst x y h := by
  exact PV_CB_Op80Source.op80_source ops inst x y h
#print axioms op80_source
#print axioms ProverRwP6BodyData.refinement_of_data
end R1Z.PV_Join_Codecs
