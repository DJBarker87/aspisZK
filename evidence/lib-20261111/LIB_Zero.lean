import LIB_Carriers
import NND_ScalarComparison
import NMT_345ZeroSource
set_option autoImplicit false
noncomputable section
namespace LIB_Zero
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier
/-- Symbolic loop result from the retained CLOSED342 support, at SAME bytes. -/
theorem bytes_all_zero (b : Slice U8) :
 (bytes b).all (· == 0) = b.val.all (· == 0#u8) := by
 simp only [bytes,List.all_map,Function.comp_def,←byte_zero,byte_beq]
theorem result (b : Slice U8) :
 r1_pool_adapter.owned.require_zero b =
 ok (if (bytes b).all (· == 0) then core.result.Result.Ok ()
     else core.result.Result.Err .AccountAlreadyInitialized) := by
 simpa only [bytes_all_zero] using NMT_345.zero_source b
#print axioms bytes_all_zero
#print axioms result
end LIB_Zero
