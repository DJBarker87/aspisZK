import Aeneas
import NCV_Reference.Funs
import PCVV_LaneDecodeRef
import PRVEq_Op50_p8
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVY_Op50
open PCVV_LaneDecodeRef (sl le)

#print Aeneas.Std.UScalar.shiftRight
#print Aeneas.Std.UScalar.shiftRight_UScalar
#check @Aeneas.Std.UScalar.shiftRight_spec
#check @Aeneas.Std.U64.ShiftRight_spec
#print Aeneas.Std.core.convert.FromSame.from
#print Aeneas.Std.UScalar.and
#check @Aeneas.Std.UScalar.val_and
#check @Aeneas.Std.UScalar.and_val
#check @Aeneas.Std.UScalar.shiftRight_val_eq
#check @Aeneas.Std.UScalar.val_shiftRight
#check @Aeneas.Std.UScalar.ShiftRight_spec
#print Aeneas.Std.lift
#check @Aeneas.Std.core.slice.index.Slice.index

/-- `DecidableEq` for the Aeneas byte-word arrays: equality of the underlying lists -/
instance instDecEqDig : DecidableEq (Std.Array U32 8#usize) := fun a b =>
  decidable_of_iff (a.val = b.val) ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem dec_arr (a b : Std.Array U32 8#usize) : decide (a = b) = decide (a.val = b.val) := by
  by_cases h : a.val = b.val
  · have : a = b := Subtype.ext h
    simp [h, this]
  · have : a ≠ b := fun e => h (congrArg Subtype.val e)
    simp [h, this]

end PCVY_Op50
