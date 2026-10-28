import R1Z.PV_RunJoin_ResultDomain28
import R1Z.BuilderForestAdmissionPort
set_option autoImplicit false
namespace R1Z.PV_RunJoin_Conservation29
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort.pool_v1

/-- The outer Rust transfer conservation guard, on natural values. The sum
cannot overflow u32 once both summands are below VALUE_LIMIT. -/
def transferDomain (input recipient change : U32) : Prop :=
  0 < recipient.val ∧ 0 < change.val ∧ recipient.val < 2^30 ∧
  change.val < 2^30 ∧ recipient.val + change.val = input.val

def withdrawalDomain (input amount change : U32) : Prop :=
  0 < change.val ∧ change.val < 2^30 ∧ amount.val + change.val = input.val

theorem sum_no_overflow (left right : U32)
    (hl : left.val < 2^30) (hr : right.val < 2^30) :
    left.val + right.val < 2^32 := by omega
#print axioms sum_no_overflow

theorem transfer_input_positive (input recipient change : U32)
    (h : transferDomain input recipient change) : 0 < input.val := by
  unfold transferDomain at h
  omega
#print axioms transfer_input_positive

theorem withdrawal_input_positive (input amount change : U32)
    (h : withdrawalDomain input amount change) : 0 < input.val := by
  unfold withdrawalDomain at h
  omega
#print axioms withdrawal_input_positive

theorem transfer_zero_change (input recipient change : U32) (h : change.val = 0) :
    ¬ transferDomain input recipient change := by
  unfold transferDomain
  omega
#print axioms transfer_zero_change

theorem transfer_zero_recipient (input recipient change : U32) (h : recipient.val = 0) :
    ¬ transferDomain input recipient change := by
  unfold transferDomain
  omega
#print axioms transfer_zero_recipient

theorem withdrawal_zero_change (input amount change : U32) (h : change.val = 0) :
    ¬ withdrawalDomain input amount change := by
  unfold withdrawalDomain
  omega
#print axioms withdrawal_zero_change
end R1Z.PV_RunJoin_Conservation29
