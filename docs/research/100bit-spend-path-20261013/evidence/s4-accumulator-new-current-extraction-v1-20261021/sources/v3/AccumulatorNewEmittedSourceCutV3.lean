import AspisR1CurrentCaller.Types
import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S4AccumulatorNewEmittedSourceCutV3
open AspisR1CurrentCaller

def mapFilled (r : core.result.Result
    (alloc.vec.Vec aspis_core.field.QM31) aspis_core.r0.Error) :
    Result (core.result.Result (alloc.vec.Vec aspis_core.field.QM31) verifier.Error) :=
  match r with
  | .Ok weights => .ok (.Ok weights)
  | .Err _ => .ok (.Err verifier.Error.Allocation)

/-- A parameterized transcription of the transparent Aeneas constructor body.
    The five external child calls remain operation inputs. `mapFilled` is the
    exact result of `Result.map_err` with the extracted closure's Allocation
    mapping; Try branch and residual propagation are retained verbatim. -/
def emittedBody
    (finalLen : transport.Variant → Result Std.Usize)
    (zeroQ : Result aspis_core.field.QM31)
    (filled : Std.Usize → aspis_core.field.QM31 → Result (core.result.Result
      (alloc.vec.Vec aspis_core.field.QM31) aspis_core.r0.Error))
    (zeroWide : Result aspis_core.field.wide_exact.WideExact)
    (oneQ : Result aspis_core.field.QM31)
    (v : transport.Variant) :
    Result (core.result.Result verifier.Accumulator verifier.Error) := do
  let i ← finalLen v
  let q ← zeroQ
  let r ← filled i q
  let r1 ← mapFilled r
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue weights => do
      let rhs ← zeroWide
      let power ← oneQ
      .ok (.Ok { weights := weights, rhs := rhs, power := power, next := 0#usize })
  | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        verifier.Accumulator (core.convert.FromSame verifier.Error) residual

theorem emittedBody_success_next_zero
    (finalLen : transport.Variant → Result Std.Usize)
    (zeroQ : Result aspis_core.field.QM31)
    (filled : Std.Usize → aspis_core.field.QM31 → Result (core.result.Result
      (alloc.vec.Vec aspis_core.field.QM31) aspis_core.r0.Error))
    (zeroWide : Result aspis_core.field.wide_exact.WideExact)
    (oneQ : Result aspis_core.field.QM31)
    (v : transport.Variant) (a : verifier.Accumulator)
    (h : emittedBody finalLen zeroQ filled zeroWide oneQ v = .ok (.Ok a)) :
    a.next = 0#usize := by
  unfold emittedBody at h
  cases hlen : finalLen v with
  | fail e => simp [hlen] at h
  | div => simp [hlen] at h
  | ok i =>
    simp only [hlen, bind_tc_ok] at h
    cases hq : zeroQ with
    | fail e => simp [hq] at h
    | div => simp [hq] at h
    | ok q =>
      simp only [hq, bind_tc_ok] at h
      cases hf : filled i q with
      | fail e => simp [hf] at h
      | div => simp [hf] at h
      | ok result =>
        simp only [hf, bind_tc_ok] at h
        cases result with
        | Err e =>
          simp [mapFilled, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
        | Ok weights =>
          simp only [mapFilled, bind_tc_ok,
            core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
          cases hz : zeroWide with
          | fail e => simp [hz] at h
          | div => simp [hz] at h
          | ok rhs =>
            simp only [hz, bind_tc_ok] at h
            cases ho : oneQ with
            | fail e => simp [ho] at h
            | div => simp [ho] at h
            | ok power =>
              simp only [ho, bind_tc_ok] at h
              cases h
              rfl

#print axioms emittedBody_success_next_zero
end AspisR1S4AccumulatorNewEmittedSourceCutV3
