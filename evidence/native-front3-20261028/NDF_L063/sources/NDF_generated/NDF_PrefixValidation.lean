import NDF_ValidatorRun
set_option autoImplicit false
noncomputable section
namespace NDF_PrefixValidation
open Aeneas Aeneas.Std Result
open AspisR1.ExtractedPrefixFieldAgreement AspisR1.ExtractedPrefixRecordAgreement

theorem error_injective : Function.Injective errorToRecord := by
  intro a b same
  cases a <;> cases b <;> simp_all [errorToRecord]

theorem status_injective {α : Type} : Function.Injective (@statusToRecord α) := by
  intro a b same
  cases a with
  | Ok a => cases b <;> cases same; rfl
  | Err a =>
    cases b with
    | Ok b => cases same
    | Err b =>
      have errors : errorToRecord a=errorToRecord b := core.result.Result.Err.inj same
      have equal := error_injective errors
      cases equal
      rfl

theorem map_injective {α β : Type} (f : α→β) (injective : Function.Injective f) :
    Function.Injective (mapResult f) := by
  intro a b same
  cases a <;> cases b <;> simp only [mapResult] at same <;> try (cases same; rfl)
  congr 1
  exact injective (Result.ok.inj same)

theorem loop (row : U8) (iter : NDF_ValidatorStep.Iter)
    (widths : ∀ chunk∈iter.iter.chunks,chunk.val.length=32) :
    mapResult statusToRecord (AspisR1PrefixAggregateParser.r1_wire.validate_record_fields_loop iter row) =
      NDF_ValidatorRun.scan row iter.count iter.iter.chunks := by
  rw [validator_loop_agreement,NDF_ValidatorRun.source row iter widths]

#print axioms error_injective
#print axioms status_injective
#print axioms map_injective
#print axioms loop
end NDF_PrefixValidation
