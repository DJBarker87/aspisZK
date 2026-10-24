import S6NativeForestDecodeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeForestDecode
open AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal

def statement_tag : PoolV1PairForestTerminalStatementV1 → U8
  | .PrivateTransfer _ _ => 1#u8
  | .Withdrawal _ _ => 2#u8

def header_frame (raw : Array U8 1880#usize) (statement : PoolV1PairForestTerminalStatementV1) : Prop :=
  List.slice 0 4 raw.val=POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC.val ∧
  raw.val[4]'(by rw [raw.property]; decide)=POOL_V1_PAIR_FOREST_TERMINAL_VERSION ∧
  raw.val[5]'(by rw [raw.property]; decide)=statement_tag statement ∧
  raw.val[6]'(by rw [raw.property]; decide)=pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION

def payment_frame (bytes : Slice U8) : PoolV1PairForestTerminalStatementV1 → Prop
  | .PrivateTransfer _ value => ∃ input : Slice U8, input.val=bytes.val.drop 1664 ∧
      pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1 input=ok (core.result.Result.Ok value)
  | .Withdrawal _ value => ∃ input : Slice U8, input.val=bytes.val.drop 1664 ∧
      pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 input=ok (core.result.Result.Ok value)

def full_frame (bytes : Slice U8) (statement : PoolV1PairForestTerminalStatementV1) : Prop :=
  (∃ raw : Array U8 1880#usize, raw.val=bytes.val ∧ header_frame raw statement) ∧
  (∃ common, PoolV1PairForestTerminalStatementV1.common statement=ok common ∧ common_frame bytes common) ∧
  payment_frame bytes statement ∧
  validate_pool_v1_pair_forest_terminal_statement_v1 statement=ok (core.result.Result.Ok ())

@[step] theorem decode_frames (bytes : Slice U8) :
    decode_pool_v1_pair_forest_terminal_statement_v1 bytes
      ⦃ result => ∀ statement, result=core.result.Result.Ok statement → full_frame bytes statement ⦄ := by
  unfold decode_pool_v1_pair_forest_terminal_statement_v1
    core.cmp.PartialEq.ne.trait_default Slice.Insts.CoreCmpPartialEqSlice
  step*
  all_goals try exact AspisS6StdByteSlice.eq_spec _ _
  all_goals step*
  all_goals trace_state

#print axioms decode_frames
end AspisS6NativeForestDecode
