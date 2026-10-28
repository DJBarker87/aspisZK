import NBN_WordArrayEq
set_option autoImplicit false
noncomputable section
namespace NBN_ArrayNe
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

theorem bytes {n : Usize} (a b : Array U8 n) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a b = ok (decide (a ≠ b)) := by
  simp [core.array.equality.PartialEqArray.ne,NBH_ArrayEq.source]

theorem words {n : Usize} (a b : Array U32 n) :
    core.array.equality.PartialEqArray.ne
      AspisR1TerminalDecoder.aspis_core.field.M31.Insts.CoreCmpPartialEqM31 a b =
      ok (decide (a ≠ b)) := by
  simp [core.array.equality.PartialEqArray.ne,NBN_WordArrayEq.source]

#print axioms bytes
#print axioms words
end NBN_ArrayNe
