import NMS_R2R20Helpers
set_option autoImplicit false
namespace NMS_R2R20ActualMaps
open Aeneas Aeneas.Std Result WP AspisR20Request
@[step] theorem map_0_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    AspisR20Request.core.result.Result.map_err pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  exact NMS_R2R20Helpers.map_0_spec r

@[step] theorem map_1_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    AspisR20Request.core.result.Result.map_err pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  exact NMS_R2R20Helpers.map_1_spec r

@[step] theorem map_2_spec {T : Type} (r : core.result.Result T core.array.TryFromSliceError) :
    AspisR20Request.core.result.Result.map_err pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  exact NMS_R2R20Helpers.map_2_spec r

@[step] theorem map_3_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    AspisR20Request.core.result.Result.map_err pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  exact NMS_R2R20Helpers.map_3_spec r

@[step] theorem map_4_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    AspisR20Request.core.result.Result.map_err pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  exact NMS_R2R20Helpers.map_4_spec r

@[step] theorem map_5_spec {T : Type} (r : core.result.Result T atomic_statement.AtomicStatementError) :
    AspisR20Request.core.result.Result.map_err pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  exact NMS_R2R20Helpers.map_5_spec r

@[step] theorem map_6_spec {T : Type} (r : core.result.Result T core.array.TryFromSliceError) :
    AspisR20Request.core.result.Result.map_err pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError r ()
      ⦃ result => ∀ value, result=core.result.Result.Ok value → r=core.result.Result.Ok value ⦄ := by
  exact NMS_R2R20Helpers.map_6_spec r

#print axioms map_0_spec
#print axioms map_1_spec
#print axioms map_2_spec
#print axioms map_3_spec
#print axioms map_4_spec
#print axioms map_5_spec
#print axioms map_6_spec
end NMS_R2R20ActualMaps
