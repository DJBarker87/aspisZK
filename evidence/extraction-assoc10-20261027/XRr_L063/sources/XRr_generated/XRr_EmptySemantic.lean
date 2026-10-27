import XRr_ObservedReject
import ExtractedPrefixParseCore
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRr_EmptySemantic
/-- A concrete malformed input reaches a real rejection, independent of any
success/refinement premise. No accepted transaction witness is asserted. -/
def empty : Slice U8 := ⟨[],by scalar_tac⟩
theorem emitted : r1_wire.Prefix.parse empty=ok (.Err (.Length 0#u8)) := by
 unfold r1_wire.Prefix.parse
 have short : Slice.len empty<32#usize := by scalar_tac
 rw [if_pos short]
theorem cohort : AspisR1PublicPreparation.PrefixAdapter.parseAccepted empty=
 ok (.Err (.Length 0#u8)) := by
 unfold AspisR1PublicPreparation.PrefixAdapter.parseAccepted
 unfold AspisR1PrefixAggregateParser.r1_wire.Prefix.parse
 have short : Slice.len empty<32#usize := by scalar_tac
 rw [if_pos short,bind_tc_ok]
 rfl
#print axioms emitted
#print axioms cohort
end XRr_EmptySemantic
