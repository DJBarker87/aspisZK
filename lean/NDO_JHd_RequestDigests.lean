import JHd_RequestFuns
import NDO_JFs_PaymentDigests
set_option autoImplicit false
namespace AspisR1.JHd_RequestDigests
open Aeneas Aeneas.Std Result
theorem decode43 : AspisR20Request.atomic_statement.decode_digest_canonical
    JFs_PaymentDigests.bytes43=ok (.Ok JFt_Digest43.value) := by
  simp only [AspisR20Request.atomic_statement.decode_digest_canonical,
    AspisR20Request.aspis_core.field.M31.from_le_bytes,AspisR20Request.aspis_core.field.P]
  rfl
#print axioms decode43
theorem decode44 : AspisR20Request.atomic_statement.decode_digest_canonical
    JFs_PaymentDigests.bytes44=ok (.Ok JFt_Digest44.value) := by
  simp only [AspisR20Request.atomic_statement.decode_digest_canonical,
    AspisR20Request.aspis_core.field.M31.from_le_bytes,AspisR20Request.aspis_core.field.P]
  rfl
#print axioms decode44
theorem decode45 : AspisR20Request.atomic_statement.decode_digest_canonical
    JFs_PaymentDigests.bytes45=ok (.Ok JFt_Digest45.value) := by
  simp only [AspisR20Request.atomic_statement.decode_digest_canonical,
    AspisR20Request.aspis_core.field.M31.from_le_bytes,AspisR20Request.aspis_core.field.P]
  rfl
#print axioms decode45
theorem decode46 : AspisR20Request.atomic_statement.decode_digest_canonical
    JFs_PaymentDigests.bytes46=ok (.Ok JFt_Digest46.value) := by
  simp only [AspisR20Request.atomic_statement.decode_digest_canonical,
    AspisR20Request.aspis_core.field.M31.from_le_bytes,AspisR20Request.aspis_core.field.P]
  rfl
#print axioms decode46
end AspisR1.JHd_RequestDigests
