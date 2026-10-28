import NCO_ValidateModel
import NCO_Framing
import NDF_PrefixValidation
import NDF_ValidatorWindows
set_option autoImplicit false
noncomputable section
namespace NDF_ValidatorReference
open Aeneas Aeneas.Std Result
open AspisR1.ExtractedPrefixRecordAgreement

def reference (row : U8) (payload : Slice U8) :
    Result (core.result.Result Unit AspisR1RecordParser.r1_wire.Error) := do
  let status ← NCO_ParserRef.validate_ref row payload
  ok (statusToRecord (NCO_Framing.result status))

theorem outcome (row : U8) (payload : Slice U8) (cap : payload.val.length≤3712) :
    reference row payload = NDF_ValidatorWindows.outcome row
      (NCO_Search.search (NDF_ValidatorWindows.bad payload) (payload.val.length/32) 0) := by
  obtain ⟨final,pending,call,result⟩ := NCO_OuterRun.run payload 0#usize cap (by scalar_tac)
  have sameBad : NCO_OuterRun.bad payload=NDF_ValidatorWindows.bad payload := by
    funext i
    exact NCO_ValidateModel.bad payload i
  unfold NCO_OuterRun.Outcome at result
  have zero : (0#usize).val=0 := by scalar_tac
  rw [zero,sameBad] at result
  unfold reference NCO_ParserRef.validate_ref
  rw [call,bind_tc_ok]
  cases found : NCO_Search.search (NDF_ValidatorWindows.bad payload) (payload.val.length/32) 0 with
  | none =>
    rw [found] at result
    obtain ⟨_,rfl⟩ := result
    rfl
  | some i =>
    rw [found] at result
    obtain ⟨position,rfl⟩ := result
    have small : i≤UScalar.cMax .Usize := by rw [←position];scalar_tac
    have equal : final=UScalar.ofNat i small := by
      apply UScalar.eq_of_val_eq
      simpa using position
    simp only [NDF_ValidatorWindows.outcome,dif_pos small,bind_tc_ok,NCO_Framing.result,
      NCO_Framing.error,statusToRecord,errorToRecord,equal]

#print axioms outcome
end NDF_ValidatorReference
