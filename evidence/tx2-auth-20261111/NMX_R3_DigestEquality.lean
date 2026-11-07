import NDB_DigestDecision
import NMX_R3_ByteCarrier
set_option autoImplicit false
namespace NMX_R3_DigestEquality
open Aeneas Aeneas.Std Result NMX_R3_ByteCarrier

theorem word_injective : Function.Injective word := by
 intro a b same
 apply UScalar.eq_of_val_eq
 have value := congrArg UInt32.toNat same
 simpa only [word_value] using value

theorem rows_injective : Function.Injective (fun a : Array U32 8#usize => a.val.map word) := by
 intro a b same
 apply Subtype.ext
 exact (List.map_inj_right (fun _ _ h => word_injective h)).mp same

theorem reflexive (a : Array U32 8#usize) : NCV_Reference.eq_digest a a = ok true := by
 rw [NDB_DigestDecision.value]
 simp only [decide_true]

theorem value (a b : Array U32 8#usize) :
 NCV_Reference.eq_digest a b = ok (a.val.map word == b.val.map word) := by
 classical
 rw [NDB_DigestDecision.value]
 congr 1
 apply Bool.eq_iff_iff.mpr
 simp only [decide_eq_true_eq, beq_iff_eq]
 exact ⟨fun h => congrArg (fun a : Array U32 8#usize => a.val.map word) h,
  fun h => rows_injective h⟩
#print axioms word_injective
#print axioms rows_injective
#print axioms reflexive
#print axioms value
end NMX_R3_DigestEquality
