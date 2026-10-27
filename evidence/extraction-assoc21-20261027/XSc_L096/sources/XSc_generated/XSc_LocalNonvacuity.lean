import XSc_ParseDriver
import XRr_EmptySemantic
import XSc_RecordFieldGeneral
import XRk_ResultTools
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSc_LocalNonvacuity
/-- The new complete fold parser has an unconditional rejected-input witness. -/
theorem rejected_parser :
 XRz_ParseFold.parse XRr_EmptySemantic.empty=
  ok (.Err (XRn_Join_Release.r1_wire.Error.Length 0#u8)) :=
 (XSc_ParseDriver.source _).symm.trans XRr_EmptySemantic.emitted
/-- Arbitrary raw word arrays have actual old-decoder Results, rather than an
assumed successful decoder invocation. This is not an accepted-transaction witness. -/
theorem decoder_total (xs : XSc_RecordFieldStep.Limbs) :
 ∃ out : Option XSc_RecordFieldTypes.OW,
 AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_limbs xs=ok out := by
 have h := XSc_RecordFieldGeneral.source xs
 unfold XSc_RecordFieldStep.mapped XRo_Join_Carriers.mapR at h
 unfold _root_.aspis_core.field.wide_exact.WideExact.from_limbs at h
 split at h
 · obtain ⟨out,run,_⟩ := XRk_ResultTools.bind_success _ _ _ h
   exact ⟨out,run⟩
 · obtain ⟨out,run,_⟩ := XRk_ResultTools.bind_success _ _ _ h
   exact ⟨out,run⟩
#print axioms rejected_parser
#print axioms decoder_total
end XSc_LocalNonvacuity
