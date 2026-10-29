import NDF_ValidatorBridge
import NDF_ParserDomain
import MultiproofConeSlices
set_option autoImplicit false
namespace NDI_ParserPayload
open Aeneas Aeneas.Std Result

theorem range (frame : Slice U8) (five : 5 ≤ frame.val.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      frame {start:=5#usize} = ok (Slice.drop frame 5#usize) :=
  AspisR1.MultiproofConeSlices.drop_total frame 5#usize (by scalar_tac)

theorem cap (frame : Slice U8) (bound : frame.val.length ≤ 3717) :
    (Slice.drop frame 5#usize).val.length ≤ 3712 := by
  simp only [Slice.drop,List.length_drop]
  scalar_tac

theorem validator (row : U8) (frame : Slice U8) (bound : frame.val.length ≤ 3717) :
    (do let status ← NCO_ParserRef.validate_ref row (Slice.drop frame 5#usize)
        ok (NCO_Framing.result status)) =
      AspisR1PrefixAggregateParser.r1_wire.validate_record_fields row (Slice.drop frame 5#usize) :=
  NDF_ValidatorBridge.reference row _ (cap frame bound)

#print axioms range
#print axioms cap
#print axioms validator
end NDI_ParserPayload
