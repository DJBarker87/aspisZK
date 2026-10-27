import R1Z.PV_CB_Op223TagFuns
import R1Z.PV_CB_CanonicalM31
set_option autoImplicit false
namespace R1Z.PV_CB_Op223TagCanonical
open Aeneas Aeneas.Std Result
abbrev base := PV_CB_ShippedOp223Tag.aspis_statement.pool_v1.pair_trace.POOL_V1_PAIR_COPY_TAG_BASE_V1

def tag (id : U16) : U32 := U32.wrapping_add base (core.convert.num.FromU32U16.from id)

/-- Exact complete Result of the extracted copy of the two shipped tag
    expressions, including their actual imported base constant. Not op223_source. -/
theorem expression (id : U16) : PV_CB_ShippedOp223Tag.copy_tag id = ok (tag id) := rfl

theorem value (id : U16) : (tag id).val = 1124073472 + id.val := by
  rw [tag,U32.wrapping_add_val_eq,core.convert.num.FromU32U16.from_val_eq]
  simp only [base,PV_CB_ShippedOp223Tag.aspis_statement.pool_v1.pair_trace.POOL_V1_PAIR_COPY_TAG_BASE_V1]
  have baseval : (1124073472#u32).val = 1124073472 := by decide
  have sizeval : UScalar.size .U32 = 4294967296 := by rw [UScalar.size_def];decide
  rw [baseval,sizeval]
  change (1124073472 + id.val) % 4294967296 = 1124073472 + id.val
  apply Nat.mod_eq_of_lt
  have bound := id.bv.isLt
  change id.val < 65536 at bound
  omega

theorem canonical (id : U16) : PV_CB_CanonicalM31.Valid (tag id) := by
  unfold PV_CB_CanonicalM31.Valid
  rw [value]
  change 1124073472 + id.val < 2147483647
  have bound := id.bv.isLt
  change id.val < 65536 at bound
  omega
#print axioms expression
#print axioms value
#print axioms canonical
end R1Z.PV_CB_Op223TagCanonical
