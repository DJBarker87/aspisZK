import Port3_FinishAny
import Port3_Wrapping
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

theorem checked_mul (x y : Usize) (small : x.val*y.val≤4096) :
    (x*y : Result Usize)=ok (Usize.wrapping_mul x y) := by
  have capacity : 4096≤Usize.max := by scalar_tac
  have spec : WP.spec (x*y : Result Usize) (fun out => out.val=x.val*y.val) := by
    apply UScalar.mul_spec
    simpa only [UScalar.max_USize_eq] using small.trans capacity
  obtain ⟨out,run,hvalue⟩ := WP.spec_imp_exists spec
  have same : out=Usize.wrapping_mul x y := UScalar.eq_of_val_eq
    (hvalue.trans (Port3_Wrapping.wrap_mul_value x y small).symm)
  exact run.trans (congrArg Result.ok same)

/-- Only the actual parent rounds are equated; no global checked/wrapping law. -/
theorem round_small (ops : FinishOps W) (poly : Slice U8) (alpha claim : E)
    (r : Usize) (small : r.val ≤ 1) :
    round ops poly alpha claim r = verifier.finishRelationRoundWithOps ops poly alpha claim r := by
  have hm : (3#usize).val*r.val ≤ 4096 := by change 3*r.val≤4096; omega
  have hv := Port3_Wrapping.wrap_mul_value 3#usize r hm
  have ha : (Usize.wrapping_mul 3#usize r).val + (1#usize).val ≤ 4096 := by
    change _ + 1 ≤ 4096; rw [hv]; change 3*r.val+1≤4096; omega
  have hb : (Usize.wrapping_mul 3#usize r).val + (2#usize).val ≤ 4096 := by
    change _ + 2 ≤ 4096; rw [hv]; change 3*r.val+2≤4096; omega
  simp only [round,verifier.finishRelationRoundWithOps,checked_mul _ _ hm,
    Port3_Wrapping.checked_add _ _ ha,Port3_Wrapping.checked_add _ _ hb,lift,bind_tc_ok]

theorem round_zero (ops : FinishOps W) (poly : Slice U8) (alpha claim : E) :
    round ops poly alpha claim 0#usize = verifier.finishRelationRoundWithOps ops poly alpha claim 0#usize :=
  round_small ops poly alpha claim 0#usize (by decide)

theorem round_one (ops : FinishOps W) (poly : Slice U8) (alpha claim : E) :
    round ops poly alpha claim 1#usize = verifier.finishRelationRoundWithOps ops poly alpha claim 1#usize :=
  round_small ops poly alpha claim 1#usize (by decide)

def native (ops : FinishOps W) : Port3_NativeFinishBody.Ops W :=
  {Port3_FinishStage.native (Port3_FinishStage.release ops) with op5 := round (Port3_FinishStage.release ops)}

theorem parent_eq (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit)) :
    Port3_NativeFinishBody.verifier.finish_relation (native ops) v p a obs =
      verifier.finishRelationWithOps (Port3_FinishStage.release ops) v p a obs := by
  unfold Port3_NativeFinishBody.verifier.finish_relation verifier.finishRelationWithOps native Port3_FinishStage.native
  simp only [round_zero,round_one]
  rfl

#print axioms checked_mul
#print axioms round_small
#print axioms round_zero
#print axioms round_one
#print axioms parent_eq
end AspisR1.Port4D_Round
end
