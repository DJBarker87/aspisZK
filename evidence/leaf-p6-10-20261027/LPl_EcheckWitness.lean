import LPl_EcheckResult
open Aeneas Aeneas.Std Result LPl_Kit_Release
set_option autoImplicit false
namespace LPl.Echeck
/-- Empty-input success and nonempty canonical success are independent concrete
    inhabitants, not witnesses for the headline's complete premise set. -/
theorem zero_chunk : chunk (List.replicate 32 (0#u8)) true = true := by decide

theorem rejected_chunk : chunk ([255#u8,255#u8,255#u8,127#u8] ++
    List.replicate 28 (0#u8)) false = false := by decide

theorem empty_result (bs : Slice U8) (empty : bs.val = []) (k : Bool) :
    verifier.echeck bs k = ok (.Ok ()) := by
  exact native_result bs k true (.done 0 (by simp [empty]))

#print axioms zero_chunk
#print axioms rejected_chunk
#print axioms empty_result
end LPl.Echeck
