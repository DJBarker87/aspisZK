import NND_AccountLaws
import NMT_345ZeroSource
set_option autoImplicit false
noncomputable section
namespace NND_Carrier
open Aeneas Aeneas.Std Result AdapterRw

theorem bytes_all_zero (b : Slice U8) :
 (bytes b).all (· == 0) = b.val.all (· == 0#u8) := by
 simp only [bytes,List.all_map,Function.comp_def,←byte_zero,byte_beq]

theorem historical_zero (b : Slice U8) :
 outer (reply id) (r1_pool_adapter.owned.require_zero b) = ok (RSL.requireZero (bytes b)) := by
 rw [NMT_345.zero_source]
 unfold RSL.requireZero
 rw [bytes_all_zero]
 cases b.val.all (· == 0#u8) <;> rfl

/-- Existing CLOSED native342 reference on its OWN bound. This does not turn
failed NND_E002 into a fresh frozen emission; that provenance gap stays listed. -/
theorem closed_zero_reference (b : Slice U8) (bound : b.val.length ≤ 4096) :
 outer (reply id) (do let x ← NFQ_ScanReference.zero_ref b; ok (NFQ_ZeroSource.result x)) =
 ok (RSL.requireZero (bytes b)) := by
 rw [←NFU_ZeroPort.source b bound]
 exact historical_zero b

#print axioms bytes_all_zero
#print axioms historical_zero
#print axioms closed_zero_reference
end NND_Carrier
end
