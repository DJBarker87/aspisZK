import AspisR20Request.Funs

/-! Exact byte identity for the pinned extracted fused normalization reference.
Kani's shipped_pipeline_normalization_equivalence proves the entire shipped
ASQ8 decode/re-encode pipeline equal to this reference for every 320-byte
input, including errors. That equivalence and the header comparator model
are named P6 evidence; no new Lean axiom is introduced here.

Success is the operational admission condition. There is no premise about
an encoder result, codec inverse, matching deterministic serializers, account
snapshot or public variant. Both payment variants are covered. Account/CPI
provenance and the R20 sameSnapshot obligation remain separate. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR20Request.ASQ8Normalization
open pool_v1.pair_forest_terminal
open pool_v1.payment_relation

abbrev Bytes := Array U8 320#usize

/-- The extracted reference preserves precisely the bytes supplied to stage 2
whenever its normalization succeeds. -/
theorem success_bytes (bytes out : Bytes)
    (h : normalize_pool_v1_pair_forest_terminal_request_reference_v1 bytes =
      ok (.Ok out)) : out = bytes := by
  unfold normalize_pool_v1_pair_forest_terminal_request_reference_v1 at h
  cases hd : decode_pool_v1_pair_forest_terminal_request_reference_v1 bytes <;>
    simp_all [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]

/-- A successful transfer decode yields the exact original ASQ8 bytes. -/
theorem transfer_bytes (bytes : Bytes)
    (profile release program : Array U8 32#usize)
    (p : PoolV1PrivateTransferPublicV1)
    (h : decode_pool_v1_pair_forest_terminal_request_reference_v1 bytes =
      ok (.Ok { verifier_profile := profile, verifier_release := release,
        pool_program := program, «public» := .PrivateTransfer p })) :
    normalize_pool_v1_pair_forest_terminal_request_reference_v1 bytes =
      ok (.Ok bytes) := by
  simp [normalize_pool_v1_pair_forest_terminal_request_reference_v1, h,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- A successful withdrawal decode yields the exact original ASQ8 bytes. -/
theorem withdrawal_bytes (bytes : Bytes)
    (profile release program : Array U8 32#usize)
    (p : PoolV1WithdrawalPublicV1)
    (h : decode_pool_v1_pair_forest_terminal_request_reference_v1 bytes =
      ok (.Ok { verifier_profile := profile, verifier_release := release,
        pool_program := program, «public» := .Withdrawal p })) :
    normalize_pool_v1_pair_forest_terminal_request_reference_v1 bytes =
      ok (.Ok bytes) := by
  simp [normalize_pool_v1_pair_forest_terminal_request_reference_v1, h,
    core.result.Result.Insts.CoreOpsTry.branch]

#print axioms success_bytes
#print axioms transfer_bytes
#print axioms withdrawal_bytes
#print axioms encode_pool_v1_pair_forest_terminal_request_reference_v1
#print axioms decode_pool_v1_pair_forest_terminal_request_reference_v1
#print axioms normalize_pool_v1_pair_forest_terminal_request_reference_v1
end AspisR20Request.ASQ8Normalization
