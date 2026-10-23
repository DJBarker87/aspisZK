import S6SourceDigestAcceptedInverseV1
import S6SourcePaymentValidatorTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.PaymentDecodeHelpers
open AspisS6FiveUnrolledCodec

@[step] theorem unwrap_ok_spec {T : Type} (copyInst : core.marker.Copy T) (value : T) :
    aspis_statement.atomic_statement.unwrap_fixed_slice copyInst (core.result.Result.Ok value)
      ⦃ result => result=value ⦄ := by
  apply exists_imp_spec
  exact ⟨value,rfl,rfl⟩

@[step] theorem branch_spec {T E : Type} (r : core.result.Result T E) :
    core.result.Result.Insts.CoreOpsTry.branch r
      ⦃ cf => ∀ value, cf=core.ops.control_flow.ControlFlow.Continue value →
        r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp

@[step] theorem map_0_spec {T : Type} (r : core.result.Result T aspis_statement.atomic_statement.AtomicStatementError) :
    core.result.Result.map_err aspis_statement.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,aspis_statement.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError,aspis_statement.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once]

@[step] theorem map_1_spec {T : Type} (r : core.result.Result T aspis_statement.atomic_statement.AtomicStatementError) :
    core.result.Result.map_err aspis_statement.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,aspis_statement.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError,aspis_statement.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once]

@[step] theorem map_2_spec {T : Type} (r : core.result.Result T core.array.TryFromSliceError) :
    core.result.Result.map_err aspis_statement.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,aspis_statement.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError,aspis_statement.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once]

@[step] theorem map_3_spec {T : Type} (r : core.result.Result T aspis_statement.atomic_statement.AtomicStatementError) :
    core.result.Result.map_err aspis_statement.pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,aspis_statement.pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError,aspis_statement.pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once]

@[step] theorem map_4_spec {T : Type} (r : core.result.Result T aspis_statement.atomic_statement.AtomicStatementError) :
    core.result.Result.map_err aspis_statement.pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,aspis_statement.pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError,aspis_statement.pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once]

@[step] theorem map_5_spec {T : Type} (r : core.result.Result T aspis_statement.atomic_statement.AtomicStatementError) :
    core.result.Result.map_err aspis_statement.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,aspis_statement.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError,aspis_statement.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once]

@[step] theorem map_6_spec {T : Type} (r : core.result.Result T core.array.TryFromSliceError) :
    core.result.Result.map_err aspis_statement.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  apply exists_imp_spec
  cases r <;> refine ⟨_,rfl,?_⟩ <;> simp [core.result.Result.map_err,aspis_statement.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError,aspis_statement.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once]

#print axioms unwrap_ok_spec
#print axioms branch_spec
end AspisS6SourceCodec.PaymentDecodeHelpers
