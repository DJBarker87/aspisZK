import CanonicalVectorSource
import CuSavingsCanonicalCandidate5
import OccupancyRangeTraversal
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalVectorLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1CanonicalDots
open CuSavingsCanonicalDotsPush CuSavingsCanonicalDotsField
open OccupancyRangeTraversal
abbrev G := Array field.wide_exact.WideExact 29#usize
variable [Shared] [VectorCommon]

theorem old_step (g : G) (iter next : Range) (dot : old_pairing.EbyKDot)
    (value : field.wide_exact.WideExact)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some iter.start,next))
    (hr : Array.index_usize g iter.start=.ok value) :
    old_callers.claim_dot_loop iter g dot = (do
      let scalar ← claim_scalar iter.start
      let (r,dot1) ← old_pairing.EbyKDot.push dot value scalar
      match r with
      | .Ok _ => old_callers.claim_dot_loop next g dot1
      | .Err _ => .ok (.Err Error.Parse)) := by
  unfold old_callers.claim_dot_loop
  rw [loop]
  dsimp only
  simp only [old_callers.claim_dot_loop.body,hn,bind_tc_ok]
  cases hs : claim_scalar iter.start with
  | fail e => simp only [hs,bind_tc_fail];rfl
  | div => simp only [hs,bind_tc_div];rfl
  | ok scalar =>
    simp only [hs,bind_tc_ok]
    change (match (do
        let (r,dot1) ← old_pairing.EbyKDot.push dot value scalar
        let r1 ← core.result.Result.map_err
          old_callers.claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError r ()
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf with
        | core.ops.control_flow.ControlFlow.Continue _ => .ok (.cont (next,dot1))
        | core.ops.control_flow.ControlFlow.Break residual => do
          let r2 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            field.wide_exact.WideExact (core.convert.FromSame Error) residual
          .ok (.done r2)) with
      | .ok (.cont state) => old_callers.claim_dot_loop state.1 g state.2
      | .ok (.done out) => .ok out
      | .fail e => .fail e
      | .div => .div) = _
    cases hp : old_pairing.EbyKDot.push dot value scalar with
    | fail e => simp only [hp,bind_tc_fail];rfl
    | div => simp only [hp,bind_tc_div];rfl
    | ok pair =>
      rcases pair with ⟨result,after⟩
      cases result <;>
        simp [hp,core.result.Result.map_err,
          old_callers.claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError,
          old_callers.claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

#print axioms old_step
end AspisR1.CuSavingsCanonicalVectorLoop
