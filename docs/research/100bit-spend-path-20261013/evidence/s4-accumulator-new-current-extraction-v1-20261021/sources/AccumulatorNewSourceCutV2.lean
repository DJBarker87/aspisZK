import AspisR1CurrentCaller.Types
import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4AccumulatorNewSourceCutV2
open AspisR1CurrentCaller

def filledMap (r : core.result.Result
    (alloc.vec.Vec aspis_core.field.QM31) aspis_core.r0.Error) :
    core.result.Result (alloc.vec.Vec aspis_core.field.QM31) verifier.Error :=
  match r with
  | .Ok weights => .Ok weights
  | .Err _ => .Err verifier.Error.Allocation

/-- Parameterized form of the exact transparent Aeneas constructor body.
    Each external child operation, including generated Result-valued constants,
    remains an explicit input. `filledMap` is the emitted `map_err` closure. -/
def accumulatorNewBody
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
  match filledMap r with
  | .Ok weights => do
      let rhs ← zeroWide
      let power ← oneQ
      .ok (.Ok { weights := weights, rhs := rhs, power := power, next := 0#usize })
  | .Err e => .ok (.Err e)

theorem accumulatorNewBody_success_next_zero
    (finalLen : transport.Variant → Result Std.Usize)
    (zeroQ : Result aspis_core.field.QM31)
    (filled : Std.Usize → aspis_core.field.QM31 → Result (core.result.Result
      (alloc.vec.Vec aspis_core.field.QM31) aspis_core.r0.Error))
    (zeroWide : Result aspis_core.field.wide_exact.WideExact)
    (oneQ : Result aspis_core.field.QM31)
    (v : transport.Variant) (a : verifier.Accumulator)
    (h : accumulatorNewBody finalLen zeroQ filled zeroWide oneQ v = .ok (.Ok a)) :
    a.next = 0#usize := by
  unfold accumulatorNewBody at h
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
        | Err e => simp [filledMap] at h
        | Ok weights =>
          simp only [filledMap, bind_tc_ok] at h
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

#print axioms accumulatorNewBody_success_next_zero
end AspisR1S4AccumulatorNewSourceCutV2
