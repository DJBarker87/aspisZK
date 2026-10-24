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
  all_goals (intro statement accepted; cases accepted)
  all_goals (have kind_byte := r_post val (cf_post val (by assumption)))
  all_goals (have common_fields := r1_post val1 (cf1_post val1 (by assumption)))
  all_goals (obtain ⟨payload,variant,payment_decoded⟩ := r2_post val2 (cf2_post val2 (by assumption)))
  all_goals (have raw_valid := cf3_post _ (by assumption))
  all_goals (have validated : r3=core.result.Result.Ok () := raw_valid.trans (congrArg core.result.Result.Ok (Subsingleton.elim _ ())))
  all_goals (rw [validated] at r3_post)
  all_goals (cases variant)
  all_goals first
    | (have hv : val=pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer := by assumption
       rw [hv] at kind_byte
       change 1#u8=i3 at kind_byte)
    | (have hv : val=pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal := by assumption
       rw [hv] at kind_byte
       change 2#u8=i3 at kind_byte)
  all_goals (have hlen : bytes.val.length=1880 := by scalar_tac)
  all_goals (unfold full_frame; refine ⟨⟨⟨bytes.val,hlen⟩,rfl,?_⟩,⟨val1,rfl,common_fields⟩,?_,r3_post⟩)
  all_goals try (solve | (unfold payment_frame; refine ⟨s2,?_,payment_decoded⟩; simpa only [i5_post] using s2_post1))
  all_goals (simp_all [header_frame,statement_tag,payment_frame,List.slice] <;> (repeat' constructor))
  all_goals first
    | scalar_tac
    | (have hm : List.take 4 POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC.val=POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC.val := by
         have h := List.take_length (l := POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC.val)
         simpa [POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC.property] using h
       exact s_post1.symm.trans hm)

#print axioms decode_frames
end AspisS6NativeForestDecode
