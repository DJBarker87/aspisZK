import NEQ_BorrowWidth
set_option autoImplicit false
noncomputable section
namespace NEQ_PaymentDomains
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem fee_primitive_width :
    (core.num.U32.to_le_bytes pool_v1.payment_relation.POOL_V1_CANONICAL_FEE).val.length=4 :=
  (core.num.U32.to_le_bytes pool_v1.payment_relation.POOL_V1_CANONICAL_FEE).property

theorem fee_zero : pool_v1.payment_relation.POOL_V1_CANONICAL_FEE=0#u32 := by
  simp only [pool_v1.payment_relation.POOL_V1_CANONICAL_FEE]

/-- Geometry discharges every fixed conversion before common/public children. -/
theorem window_bounds :
    8+32≤216 ∧ 40+32≤216 ∧ 72+8≤216 ∧ 80+32≤216 ∧ 112+32≤216 ∧
    144+4≤216 ∧ 148+4≤216 ∧ 152+32≤216 ∧ 184+32=216 := by decide

#print axioms fee_primitive_width
#print axioms fee_zero
#print axioms window_bounds
end NEQ_PaymentDomains
