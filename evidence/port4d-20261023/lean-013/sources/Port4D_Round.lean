import Port3_FinishAny
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4D_Round
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
variable {W : Type}
def round (ops : FinishOps W)
  (poly : Slice Std.U8) (alpha : aspis_core.field.wide_exact.WideExact)
  (claim : aspis_core.field.wide_exact.WideExact) (round : Std.Usize) :
  Result (core.result.Result aspis_core.field.wide_exact.WideExact
    verifier.Error)
  := do
  let we ← ops.field poly 0#usize
  let we1 ← ops.field poly 4#usize
  let lhs ← ops.add we we1
  let m ← ops.quarter
  let rhs ← ops.mulM claim m
  let i ← lift (Std.Usize.wrapping_mul 3#usize round)
  ops.trace 15#u16 i lhs
  let i1 ← lift (Std.Usize.wrapping_mul 3#usize round)
  let i2 ← lift (Std.Usize.wrapping_add i1 1#usize)
  ops.trace 15#u16 i2 rhs
  let b ←
    ops.ne lhs
      rhs
  if b
  then ok (core.result.Result.Err verifier.Error.Relation)
  else
    let claim1 ← ops.polynomial poly alpha
    let i3 ← lift (Std.Usize.wrapping_mul 3#usize round)
    let i4 ← lift (Std.Usize.wrapping_add i3 2#usize)
    ops.trace 15#u16 i4 claim1
    ok (core.result.Result.Ok claim1)

/-- Native trace indices are wrapping, while the retained control helper
uses checked indices. Only the ACTUAL parent rounds 0 and 1 are equated. -/
theorem round_zero (ops : FinishOps W) (poly : Slice U8) (alpha claim : E) :
    round ops poly alpha claim 0#usize = verifier.finishRelationRoundWithOps ops poly alpha claim 0#usize := by
  rfl

theorem round_one (ops : FinishOps W) (poly : Slice U8) (alpha claim : E) :
    round ops poly alpha claim 1#usize = verifier.finishRelationRoundWithOps ops poly alpha claim 1#usize := by
  rfl

def native (ops : FinishOps W) : Port3_NativeFinishBody.Ops W :=
  {Port3_FinishStage.native (Port3_FinishStage.release ops) with op5 := round (Port3_FinishStage.release ops)}

theorem parent_eq (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit)) :
    Port3_NativeFinishBody.verifier.finish_relation (native ops) v p a obs =
      verifier.finishRelationWithOps (Port3_FinishStage.release ops) v p a obs := by
  unfold Port3_NativeFinishBody.verifier.finish_relation verifier.finishRelationWithOps native Port3_FinishStage.native
  simp only [round_zero,round_one]

#print axioms round_zero
#print axioms round_one
#print axioms parent_eq
end AspisR1.Port4D_Round
end
