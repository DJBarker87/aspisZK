import S6NativePaymentEncodeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeForestHelpers
open AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal

theorem canonical_eq (digest : Array U32 8#usize) :
    pool_v1.pair_forest_accounts.digest_is_canonical digest=
      pool_v1.pair_tree_profile.digest_is_canonical digest := by
  unfold pool_v1.pair_forest_accounts.digest_is_canonical
    pool_v1.pair_forest_accounts.digest_is_canonical_loop
    pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
    pool_v1.pair_tree_profile.digest_is_canonical
    pool_v1.pair_tree_profile.digest_is_canonical_loop
    pool_v1.pair_tree_profile.digest_is_canonical_loop.body
  rfl

@[step] theorem canonical_spec (digest : Array U32 8#usize) :
    pool_v1.pair_forest_accounts.digest_is_canonical digest ⦃ _ => True ⦄ := by
  rw [canonical_eq]
  exact AspisS6NativeAfterstateValidatorTotal.canonical_spec digest

@[step] theorem first_byte_spec (digest : Array U32 8#usize) :
    pool_v1.pair_forest_accounts.first_canonical_byte digest ⦃ _ => True ⦄ := by
  unfold pool_v1.pair_forest_accounts.first_canonical_byte
  step*

@[step] theorem lane_spec (digest : Array U32 8#usize) :
    pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 digest ⦃ _ => True ⦄ := by
  unfold pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1
  step*

@[step] theorem common_spec (statement : PoolV1PairForestTerminalStatementV1) :
    PoolV1PairForestTerminalStatementV1.common statement ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  cases statement <;> exact ⟨_,rfl,trivial⟩

@[step] theorem public_spec (statement : PoolV1PairForestTerminalStatementV1) :
    statement_public_common statement ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  cases statement <;> exact ⟨_,rfl,trivial⟩

private theorem allM_total {T : Type} (f : T → Result Bool)
    (hf : ∀ x, ∃ b, f x=ok b) (xs : List T) :
    ∃ b, List.allM f xs=ok b := by
  induction xs with
  | nil => exact ⟨true,rfl⟩
  | cons x xs ih =>
    obtain ⟨b,hb⟩ := hf x
    simp only [List.allM,hb,bind_tc_ok]
    cases b
    · exact ⟨false,rfl⟩
    · exact ih

@[step] theorem digest_eq_spec (a b : Array U32 8#usize) :
    core.array.equality.PartialEqArray.eq aspis_core.field.M31.Insts.CoreCmpPartialEqM31 a b ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  suffices h : ∃ result, core.array.equality.PartialEqArray.eq aspis_core.field.M31.Insts.CoreCmpPartialEqM31 a b=ok result by
    obtain ⟨result,hr⟩ := h
    exact ⟨result,hr,trivial⟩
  unfold core.array.equality.PartialEqArray.eq
  split
  · apply allM_total
    intro pair
    exact ⟨_,rfl⟩
  · exact ⟨false,rfl⟩

@[step] theorem digest_ne_spec (a b : Array U32 8#usize) :
    core.array.equality.PartialEqArray.ne aspis_core.field.M31.Insts.CoreCmpPartialEqM31 a b ⦃ _ => True ⦄ := by
  unfold core.array.equality.PartialEqArray.ne
  step*

@[step] theorem bytes_ne_spec {N : Usize} (a b : Array U8 N) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a b ⦃ _ => True ⦄ := by
  unfold core.array.equality.PartialEqArray.ne
  step*

@[step] theorem map_0_spec {T : Type} (r : core.result.Result T pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) :
    core.result.Result.map_err pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1 r () ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  cases r <;> simp [core.result.Result.map_err,pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1,pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once]

@[step] theorem map_1_spec {T : Type} (r : core.result.Result T pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) :
    core.result.Result.map_err pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1 r () ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  cases r <;> simp [core.result.Result.map_err,pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1,pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once]

@[step] theorem map_2_spec {T : Type} (r : core.result.Result T pool_v1.payment_relation.PoolV1PaymentStatementFormatError) :
    core.result.Result.map_err pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1 r () ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  cases r <;> simp [core.result.Result.map_err,pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1,pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1.call_once]

@[step] theorem map_3_spec {T : Type} (r : core.result.Result T pool_v1.payment_relation.PoolV1PaymentStatementFormatError) :
    core.result.Result.map_err pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1 r () ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  cases r <;> simp [core.result.Result.map_err,pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1,pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1.call_once]

@[step] theorem map_4_spec {T : Type} (r : core.result.Result T pool_v1.payment_relation.PoolV1PaymentStatementFormatError) :
    core.result.Result.map_err pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1 r () ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  cases r <;> simp [core.result.Result.map_err,pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1,pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1.call_once]

@[step] theorem map_5_spec {T : Type} (r : core.result.Result T pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) :
    core.result.Result.map_err pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1 r () ⦃ _ => True ⦄ := by
  apply exists_imp_spec
  cases r <;> simp [core.result.Result.map_err,pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1,pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once]

#print axioms canonical_spec
#print axioms lane_spec
#print axioms digest_eq_spec
#print axioms digest_ne_spec
#print axioms bytes_ne_spec
end AspisS6NativeForestHelpers
