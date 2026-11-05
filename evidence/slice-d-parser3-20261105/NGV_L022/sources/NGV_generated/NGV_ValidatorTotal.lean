import NGV_Validator
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_ValidatorTotal
open AspisR1PrefixAggregateParser
theorem result (row : U8) (bytes : Slice U8) (bound : bytes.val.length≤3712) :
 ∃ reply : core.result.Result Unit r1_wire.Error,
 r1_wire.validate_record_fields row bytes=ok reply ∧
 NGD_ParseReference.mapResult NGO_ValidatorErrors.mapError
  (NFU_Retarget.r1_wire.validate_record_fields row bytes)=ok reply := by
 obtain ⟨out,trace⟩:=NFU_Retarget.LPl.Validate.total bytes.val
 have model:=NFU_CompactLeaves.validate_result row bytes out bound trace
 rw [NGV_Validator.result row bytes bound]
 cases out with
 | none => exact ⟨.Ok (),by rw [model];rfl,by rw [model];rfl⟩
 | some i =>
   have small: i≤UScalar.cMax .Usize := (NFU_Retarget.LPl.Validate.error_bound bytes i bound trace).2
   rw [dif_pos small] at model
   refine ⟨.Err (.NonCanonical row (UScalar.ofNat i small)),?_,?_⟩ <;> rw [model] <;> rfl
#print axioms result
end NGV_ValidatorTotal
