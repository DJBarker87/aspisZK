import NJQ_RegistryCut
import NJQ_EntryCut
set_option autoImplicit false
namespace NJQ_ResultCuts
open Aeneas Aeneas.Std Result

/-- Exhaustive errors plus accepted-value coordinates determine a FULL Rust
Result. This is a composition helper; neither input clause is native credit. -/
theorem full_result {A E : Type} (actual expected : core.result.Result A E)
 (errors : ∀ e,actual=.Err e ↔ expected=.Err e)
 (values : ∀ a b,actual=.Ok a → expected=.Ok b → a=b) : actual=expected := by
 cases actual with
 | Err e=>exact ((errors e).mp rfl).symm
 | Ok a=>
  cases expected with
  | Err e=>have bad:=(errors e).mpr rfl;cases bad
  | Ok b=>exact congrArg core.result.Result.Ok (values a b rfl rfl)

theorem registry (b : Slice U8) (len : b.val.length=128)
 (actual expected : core.result.Result NJI_V1Carrier.R NJI_V1Carrier.F)
 (errors : ∀ e,actual=.Err e ↔ expected=.Err e)
 (native_values : ∀ p,actual=.Ok p → NJQ_RegistryCut.Coordinates b len p)
 (model_values : ∀ p,expected=.Ok p → NJQ_RegistryCut.Coordinates b len p) : actual=expected := by
 apply full_result actual expected errors
 intro a q ha hq
 exact (NJQ_RegistryCut.complete_record b len a (native_values a ha)).trans
  (NJQ_RegistryCut.complete_record b len q (model_values q hq)).symm

theorem entry (b : Slice U8) (len : b.val.length=192)
 (actual expected : core.result.Result NJI_V1Carrier.E NJI_V1Carrier.F)
 (errors : ∀ e,actual=.Err e ↔ expected=.Err e)
 (native_values : ∀ p,actual=.Ok p → NJQ_EntryCut.Coordinates b len p)
 (model_values : ∀ p,expected=.Ok p → NJQ_EntryCut.Coordinates b len p) : actual=expected := by
 apply full_result actual expected errors
 intro a q ha hq
 exact (NJQ_EntryCut.complete_record b len a (native_values a ha)).trans
  (NJQ_EntryCut.complete_record b len q (model_values q hq)).symm

#print axioms full_result
#print axioms registry
#print axioms entry
end NJQ_ResultCuts
