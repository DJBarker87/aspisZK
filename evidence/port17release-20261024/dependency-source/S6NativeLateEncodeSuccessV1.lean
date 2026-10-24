import S6NativeLateEncodeAcceptedV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeLateEncodeAccepted
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

theorem encode_from_decode (bytes : Slice U8) (statement : PoolV1PairLatePublicStatementV1)
    (accepted : decode_pool_v1_pair_late_public_statement_boxed_v1 bytes=ok (core.result.Result.Ok statement))
    (output : Slice U8) (size : output.length=1520) :
    ∃ updated : Slice U8,
      encode_pool_v1_pair_late_public_statement_v1 statement output=ok (core.result.Result.Ok (),updated) ∧
      updated.length=1520 := by
  obtain ⟨snapshot_validated,afterstate_validated,checked⟩ :=
    AspisS6NativeLateDecodeTotal.accepted_validity bytes statement accepted
  obtain ⟨⟨status,updated⟩,run,success,len⟩ := spec_imp_exists
    (encode_valid_spec statement output size snapshot_validated afterstate_validated checked)
  change status=core.result.Result.Ok () at success
  rw [success] at run
  exact ⟨updated,run,len⟩

#print axioms encode_from_decode
end AspisS6NativeLateEncodeAccepted
