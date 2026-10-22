import S4FullQueryValuesPrefixV1
import S4P6PowersQueryJoinV1
import S4TailWideAddCurrentV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S4ReturnedValueTransportV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1S4P6PowersQueryJoinV1

/-- Nominal owner changes preserve all eight source coordinates and their
field interpretation, without a canonicality premise. -/
theorem returned_value_decode (x : CurrentWide) :
    AspisR1CurrentPreparedClaim.Concrete.decode (stage2ToClaim (currentWideToFull x)) =
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x) := by
  rfl

theorem returned_array_decode {n : Usize} (xs : Array CurrentWide n) :
    (currentArrayToFull xs).val.map
        (fun x => AspisR1CurrentPreparedClaim.Concrete.decode (stage2ToClaim x)) =
      xs.val.map (fun x => AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) := by
  simp only [currentArrayToFull, List.map_map, Function.comp_def, returned_value_decode]

theorem same_returned_array_decode {n : Usize}
    (current : Array CurrentWide n) (actual : Array FullWide n)
    (hsame : currentArrayToFull current = actual) :
    actual.val.map (fun x => AspisR1CurrentPreparedClaim.Concrete.decode (stage2ToClaim x)) =
      current.val.map (fun x => AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) := by
  rw [← hsame]
  exact returned_array_decode current
#print axioms returned_value_decode
#print axioms returned_array_decode
#print axioms same_returned_array_decode
end AspisR1.S4ReturnedValueTransportV1
