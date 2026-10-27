import XSe_ByteDecoder
import XSc_LocalNonvacuity
import XRk_ResultTools
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_ByteNonvacuity
/-- Every byte input has an actual old decoder result, without a successful
transaction assumption. This witnesses the transport's total arbitrary-input domain. -/
theorem source (s : Slice U8) :
 ∃ out : Option XSc_RecordFieldTypes.OW,
 AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_le_bytes s=ok out := by
 have h := XSe_ByteDecoder.source s
 unfold XSc_RecordByteLength.mapped XRo_Join_Carriers.mapR at h
 unfold _root_.aspis_core.field.wide_exact.WideExact.from_le_bytes at h
 split at h
 · obtain ⟨out,run,_⟩ := XRk_ResultTools.bind_success _ _ _ h
   exact ⟨out,run⟩
 · obtain ⟨out,run,_⟩ := XRk_ResultTools.bind_success _ _ _ h
   exact ⟨out,run⟩
#print axioms source
end XSe_ByteNonvacuity
