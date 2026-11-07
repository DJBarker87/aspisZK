import NMS_R2R20Payment
set_option autoImplicit false
namespace NMS_R2RequestMaps
open Aeneas Aeneas.Std Result WP AspisR20Request
@[step] theorem map0 {T : Type} (r : core.result.Result T pool_v1.payment_relation.PoolV1PaymentStatementFormatError) :
 AspisR20Request.core.result.Result.map_err pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1 r ()
  ⦃ result => ∀ value, result = core.result.Result.Ok value → r = core.result.Result.Ok value ⦄ := by
 apply exists_imp_spec
 cases r <;> refine ⟨_,rfl,?_⟩ <;>
  simp [AspisR20Request.core.result.Result.map_err,pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1,pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1.call_once]
@[step] theorem map1 {T : Type} (r : core.result.Result T pool_v1.payment_relation.PoolV1PaymentStatementFormatError) :
 AspisR20Request.core.result.Result.map_err pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1 r ()
  ⦃ result => ∀ value, result = core.result.Result.Ok value → r = core.result.Result.Ok value ⦄ := by
 apply exists_imp_spec
 cases r <;> refine ⟨_,rfl,?_⟩ <;>
  simp [AspisR20Request.core.result.Result.map_err,pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1,pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1.call_once]
@[step] theorem map2 {T : Type} (r : core.result.Result T core.array.TryFromSliceError) :
 AspisR20Request.core.result.Result.map_err pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r ()
  ⦃ result => ∀ value, result = core.result.Result.Ok value → r = core.result.Result.Ok value ⦄ := by
 apply exists_imp_spec
 cases r <;> refine ⟨_,rfl,?_⟩ <;>
  simp [AspisR20Request.core.result.Result.map_err,pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1,pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1.call_once]
@[step] theorem map3 {T : Type} (r : core.result.Result T core.array.TryFromSliceError) :
 AspisR20Request.core.result.Result.map_err pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r ()
  ⦃ result => ∀ value, result = core.result.Result.Ok value → r = core.result.Result.Ok value ⦄ := by
 apply exists_imp_spec
 cases r <;> refine ⟨_,rfl,?_⟩ <;>
  simp [AspisR20Request.core.result.Result.map_err,pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1,pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1.call_once]
@[step] theorem map4 {T : Type} (r : core.result.Result T core.array.TryFromSliceError) :
 AspisR20Request.core.result.Result.map_err pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1 r ()
  ⦃ result => ∀ value, result = core.result.Result.Ok value → r = core.result.Result.Ok value ⦄ := by
 apply exists_imp_spec
 cases r <;> refine ⟨_,rfl,?_⟩ <;>
  simp [AspisR20Request.core.result.Result.map_err,pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1,pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1.call_once]
#print axioms map0
#print axioms map1
#print axioms map2
#print axioms map3
#print axioms map4
end NMS_R2RequestMaps
