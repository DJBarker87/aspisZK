import NHM_HighDot
set_option autoImplicit false
noncomputable section
namespace NHM_SharedHigh
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues FIo_Native
def reference
  (partials : Array aspis_core.field.wide_exact.WideExact 4#usize)
  (w : _root_.FIo_Native.weights.Weights)
  (ap0 : Array aspis_core.field.wide_exact.WideExact 4#usize)
  (ap1 : Array aspis_core.field.wide_exact.WideExact 4#usize)
  (parts : Array aspis_core.field.wide_exact.WideExact 7#usize) :
  Result ((core.result.Result Unit verifier.Error) × (Array
    aspis_core.field.wide_exact.WideExact 7#usize))
  := do
  let a ← Array.index_usize w.factors 0#usize
  let a1 ← Array.index_usize a 4#usize
  let r ← NHM_HighDot.reference partials a1
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let a2 ← Array.index_usize a 0#usize
    let we ← _root_.FIo_Native.weights.Weights.scalar_factor a2 ap0
    let a3 ← Array.index_usize a 1#usize
    let we1 ← _root_.FIo_Native.weights.Weights.scalar_factor a3 ap1
    let scale0 ← aspis_core.field.wide_exact.WideExact.mul we we1
    let we2 ← aspis_core.field.wide_exact.WideExact.mul scale0 val
    let (_, index_mut_back) ← Array.index_mut_usize parts 1#usize
    let a4 ← Array.index_usize w.factors 2#usize
    let a5 ← Array.index_usize a4 4#usize
    let r1 ← NHM_HighDot.reference partials a5
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let a6 ← Array.index_usize a4 0#usize
      let we3 ← _root_.FIo_Native.weights.Weights.scalar_factor a6 ap0
      let a7 ← Array.index_usize a4 1#usize
      let we4 ← _root_.FIo_Native.weights.Weights.scalar_factor a7 ap1
      let scale2 ← aspis_core.field.wide_exact.WideExact.mul we3 we4
      let we5 ← aspis_core.field.wide_exact.WideExact.mul scale2 val1
      let parts1 := index_mut_back we2
      let parts2 ← Array.update parts1 3#usize we5
      ok (core.result.Result.Ok (), parts2)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame verifier.Error) residual
      let parts1 := index_mut_back we2
      ok (r2, parts1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame verifier.Error) residual
    ok (r1, parts)


/-- Two SAME high_dot calls and the exact first-error/parts[1]/parts[3] chain.
Scalar/product packets remain explicit in the suffix; native parent cuts OPEN. -/
theorem cohort (partials : Array NE 4#usize) (w : FIo_Native.weights.Weights)
 (ap0 ap1 : Array NE 4#usize) (parts : Array NE 7#usize) :
 FIo_Native.weights.shared_high partials w ap0 ap1 parts=reference partials w ap0 ap1 parts := by
 unfold FIo_Native.weights.shared_high reference
 simp only [NHM_HighDot.cohort]
 rfl

#print axioms cohort
end NHM_SharedHigh
end
