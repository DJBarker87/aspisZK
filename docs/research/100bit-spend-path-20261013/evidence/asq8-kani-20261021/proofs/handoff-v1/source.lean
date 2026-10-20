import ASQ8Normalization
import R20PoolHintStrip

/-! The actual extracted Pool suffix strip feeds exactly the bytes preserved
by the Kani-certified normalization reference. The four hint bytes are not
assumed authenticated here; account/PDA/runtime provenance stays under P2.
This concerns the 320-byte ASQ8 CPI input. The 1880-byte reconstructed ASF8
statement and R20's sameSnapshot account-field agreement remain distinct. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR20Request.ASQ8PoolHandoff
open ASQ8Normalization pool_v1.pair_forest_terminal pool_v1.payment_relation

/-- Exact Pool stripping plus normalization preserves every verifier-input
byte. There is no generic encoder or encoder-equality hypothesis. -/
theorem handoff_bytes (payload : Slice U8) (bytes out : Bytes)
    (a b c d : U8)
    (hp : payload.val = bytes.val ++ [a,b,c,d])
    (hn : normalize_pool_v1_pair_forest_terminal_request_reference_v1 bytes =
      ok (.Ok out)) :
    ∃ body hints,
      AspisR20Pool.pair_forest.split_pair_forest_terminal_bump_hints_v1 payload =
        ok (.Ok (body,hints)) ∧ body.val = out.val := by
  have hlen : payload.val.length = 324 := by simp [hp, bytes.property]
  obtain ⟨body,hints,hs,hb,_⟩ :=
    AspisR20Pool.HintStrip.strip_total_exact payload (by omega)
  refine ⟨body,hints,hs,?_⟩
  rw [ASQ8Normalization.success_bytes bytes out hn, hb, hlen, hp]
  have htake : (bytes.val ++ [a,b,c,d]).take 320 = bytes.val := by
    rw [List.take_append_of_le_length (by simp [bytes.property]),
      List.take_of_length_le (by simp [bytes.property])]
  exact htake

theorem transfer_handoff (payload : Slice U8) (bytes : Bytes)
    (a b c d : U8) (hp : payload.val = bytes.val ++ [a,b,c,d])
    (profile release program : Array U8 32#usize) (p : PoolV1PrivateTransferPublicV1)
    (hd : decode_pool_v1_pair_forest_terminal_request_reference_v1 bytes =
      ok (.Ok (.mk profile release program (.PrivateTransfer p)))) :
    ∃ body hints,
      AspisR20Pool.pair_forest.split_pair_forest_terminal_bump_hints_v1 payload =
        ok (.Ok (body,hints)) ∧ body.val = bytes.val :=
  handoff_bytes payload bytes bytes a b c d hp
    (ASQ8Normalization.transfer_bytes bytes profile release program p hd)

theorem withdrawal_handoff (payload : Slice U8) (bytes : Bytes)
    (a b c d : U8) (hp : payload.val = bytes.val ++ [a,b,c,d])
    (profile release program : Array U8 32#usize) (p : PoolV1WithdrawalPublicV1)
    (hd : decode_pool_v1_pair_forest_terminal_request_reference_v1 bytes =
      ok (.Ok (.mk profile release program (.Withdrawal p)))) :
    ∃ body hints,
      AspisR20Pool.pair_forest.split_pair_forest_terminal_bump_hints_v1 payload =
        ok (.Ok (body,hints)) ∧ body.val = bytes.val :=
  handoff_bytes payload bytes bytes a b c d hp
    (ASQ8Normalization.withdrawal_bytes bytes profile release program p hd)

#print axioms handoff_bytes
#print axioms transfer_handoff
#print axioms withdrawal_handoff
end AspisR20Request.ASQ8PoolHandoff
