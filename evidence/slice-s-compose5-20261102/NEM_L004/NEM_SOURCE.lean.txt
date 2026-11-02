import NEJ_ConcreteFrame
import NEM_PaymentReached
set_option autoImplicit false
noncomputable section
namespace NEM_PaymentFrame
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

/-- The common child preserves the transfer's canonical fee word from the
actual zero-initialized caller allocation, before either suffix write. -/
theorem common_reserved (magic : Array U8 4#usize)
    (kind : pool_v1.historical_anchor.PoolV1TransitionKind)
    (c : pool_v1.payment_relation.CommonPublicV1) (k : Nat)
    (lower : 148 ≤ k) (upper : k < 152) :
    (NBP_CommonBytes.encoded (Array.repeat 216#usize 0#u8) magic kind c).val[k]? =
      some 0#u8 := by
  rw [NEJ_ConcreteFrame.encoded_frame _ magic kind c k (Or.inr lower)]
  change (List.replicate 216 (0#u8))[k]? = some 0#u8
  rw [List.getElem?_replicate]
  exact if_pos (by omega)

/-- The complete emitted transfer reply remains paired with the same arbitrary
external state; no successful-validator premise excludes rejection paths. -/
theorem transfer_reply {State : Type} (p : NBN_ValidatorSummary.Transfer) (state : State) :
    (pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 p,state) =
      (ok (NBP_PaymentModel.transfer_encoded p),state) := by
  rw [← NED_CodecComposition.transfer_law p]

theorem withdrawal_reply {State : Type} (p : NBN_ValidatorSummary.Withdrawal) (state : State) :
    (pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 p,state) =
      (ok (NBP_PaymentModel.withdrawal_encoded p),state) := by
  rw [← NED_CodecComposition.withdrawal_law p]

#print axioms common_reserved
#print axioms transfer_reply
#print axioms withdrawal_reply
end NEM_PaymentFrame
