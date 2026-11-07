import NNH_BoxOk
set_option autoImplicit false
namespace NNH_RawOptionOk
open Aeneas Aeneas.Std

theorem value {A B F : Type} (f : A → B) (raw : Result (core.result.Result A F)) (b : B)
 (h : LIBB_ResultTotal.mapOuter (LIBB_V1DecoderValues.asOption f) raw=.ok (some b)) :
 ∃ a,raw=.ok (.Ok a) ∧ f a=b := by
 cases raw with
 | fail e => cases h
 | div => cases h
 | ok reply => cases reply with
   | Err e => cases h
   | Ok a => exact ⟨a,rfl,Option.some.inj (Result.ok.inj h)⟩
#print axioms value
end NNH_RawOptionOk
