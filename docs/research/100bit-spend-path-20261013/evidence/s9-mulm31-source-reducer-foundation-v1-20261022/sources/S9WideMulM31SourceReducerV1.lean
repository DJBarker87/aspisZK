import AspisR1S9WideMulM31CutV1.Funs

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideMulM31SourceReducerV1

/-- The reducer's exact source-shaped wrapping fold. Keeping the Std wrappers
here avoids prematurely identifying them with the generic UScalar model. -/
def sourceWrappingFold (x : Std.U64) : Std.U64 :=
  Std.U64.wrapping_add
    (x &&& (UScalar.cast .U64 AspisR1S9WideMulM31CutV1.field.P))
    (Std.U64.wrapping_shr x 31#u32)

def sourceWrappingReduce (x : Std.U64) : Std.U32 :=
  let n := UScalar.cast .U32 (sourceWrappingFold (sourceWrappingFold x))
  if n >= AspisR1S9WideMulM31CutV1.field.P then
    Std.U32.wrapping_sub n AspisR1S9WideMulM31CutV1.field.P
  else n

/-- The generated reducer source has this exact source-wrapper result. This
leaf does not yet identify the Std wrappers with R22's generic scalar model. -/
theorem source_reduce_u64_eq_sourceWrappingReduce (x : Std.U64) :
    AspisR1S9WideMulM31CutV1.field.reduce_u64 x = .ok (sourceWrappingReduce x) := by
  simp only [AspisR1S9WideMulM31CutV1.field.reduce_u64,
    AspisR1S9WideMulM31CutV1.field.P,
    sourceWrappingReduce, sourceWrappingFold, lift, bind_tc_ok]
  split_ifs <;> rfl

#print axioms source_reduce_u64_eq_sourceWrappingReduce

end AspisR1S9WideMulM31SourceReducerV1
