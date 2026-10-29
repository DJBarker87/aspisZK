import NED_DigestCohorts
import NBN_LatePrepare
set_option autoImplicit false
noncomputable section
namespace NED_PrimitiveResolution
open Aeneas Aeneas.Std Result

/-- The M31 wrapper exposes its raw U32 bytes on ALL words. It does not
invoke a WideExact serializer and adds no canonicality precondition. -/
theorem m31 (v : U32) :
    AspisR1TerminalDecoder.aspis_core.field.M31.to_le_bytes v =
    ok (core.num.U32.to_le_bytes v) := by rfl

theorem raw_m31 (v : U32) :
    AspisR1AdapterReconstruct.aspis_core.field.M31.to_le_bytes v =
    ok (core.num.U32.to_le_bytes v) := by rfl

/-- The complete late-header source law exposes only U16/U32 primitive
serialization at its four integer call sites; all mutable output frames are
retained by the source law. -/
theorem late_header {T : Type} (out : Slice U8) (size : out.length = 1520)
    (continuation : Slice U8 → Result T) :
    NBN_LatePrepare.run out continuation = continuation (NBN_LatePrepare.value out) :=
  NBN_LatePrepare.exact out size continuation

theorem sequence_width (s : NBN_StatementResult.Statement) :
    (core.num.U64.to_le_bytes (NBN_StatementResult.common s).checkpoint_sequence).val.length = 8 :=
  (core.num.U64.to_le_bytes (NBN_StatementResult.common s).checkpoint_sequence).property

theorem amount_width (p : NBN_ValidatorSummary.Withdrawal) :
    (core.num.U32.to_le_bytes p.amount).val.length = 4 :=
  (core.num.U32.to_le_bytes p.amount).property

#print axioms m31
#print axioms raw_m31
#print axioms late_header
#print axioms sequence_width
#print axioms amount_width
end NED_PrimitiveResolution
