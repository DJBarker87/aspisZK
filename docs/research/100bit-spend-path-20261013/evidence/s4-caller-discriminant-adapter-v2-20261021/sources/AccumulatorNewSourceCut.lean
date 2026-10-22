import AspisR1CurrentCaller.Types
import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4AccumulatorNewSourceCutV1
open AspisR1CurrentCaller

/-- The constructor's recorded Rust body after the two external child calls:
    final_len and heap.filled. The error map and four-way Result behavior are
    kept explicit; the Ok record has the source fields and literal next=0. -/
def filledMap (r : core.result.Result
    (alloc.vec.Vec aspis_core.field.QM31) aspis_core.r0.Error) :
    core.result.Result (alloc.vec.Vec aspis_core.field.QM31) verifier.Error :=
  match r with
  | .Ok weights => .Ok weights
  | .Err _ => .Err verifier.Error.Allocation

def accumulatorNewBody
    (finalLen : transport.Variant → Result Std.Usize)
    (filled : Std.Usize → aspis_core.field.QM31 → Result (core.result.Result
      (alloc.vec.Vec aspis_core.field.QM31) aspis_core.r0.Error))
    (zeroQ : aspis_core.field.QM31)
    (zeroWide : aspis_core.field.wide_exact.WideExact)
    (oneQ : aspis_core.field.QM31)
    (v : transport.Variant) :
    Result (core.result.Result verifier.Accumulator verifier.Error) := do
  let i ← finalLen v
  let r ← filled i zeroQ
  match filledMap r with
  | .Ok weights => .ok (.Ok {
      weights := weights
      rhs := zeroWide
      power := oneQ
      next := 0#usize })
  | .Err e => .ok (.Err e)

theorem accumulatorNewBody_success_next_zero
    (finalLen : transport.Variant → Result Std.Usize)
    (filled : Std.Usize → aspis_core.field.QM31 → Result (core.result.Result
      (alloc.vec.Vec aspis_core.field.QM31) aspis_core.r0.Error))
    (zeroQ : aspis_core.field.QM31)
    (zeroWide : aspis_core.field.wide_exact.WideExact)
    (oneQ : aspis_core.field.QM31)
    (v : transport.Variant) (a : verifier.Accumulator)
    (h : accumulatorNewBody finalLen filled zeroQ zeroWide oneQ v = .ok (.Ok a)) :
    a.next = 0#usize := by
  unfold accumulatorNewBody at h
  cases hlen : finalLen v with
  | fail e => simp [hlen] at h
  | div => simp [hlen] at h
  | ok i =>
    simp only [hlen, bind_tc_ok] at h
    cases hf : filled i zeroQ with
    | fail e => simp [hf] at h
    | div => simp [hf] at h
    | ok result =>
      cases result with
      | Err e => simp [hf, filledMap] at h
      | Ok weights =>
        simp only [hf, filledMap, bind_tc_ok] at h
        cases h
        rfl

end AspisR1S4AccumulatorNewSourceCutV1
#print axioms AspisR1S4AccumulatorNewSourceCutV1.accumulatorNewBody_success_next_zero
