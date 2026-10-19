import AspisR1BatchedWeightsExtraction.Funs
import BatchedWeightsVecResizeLengthGenericV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1BatchedWeightsExtraction
namespace BatchedWeightsFilledLengthGenericV5

theorem filled_success_length {T : Type} (copyInst : core.marker.Copy T)
    (n : Std.Usize) (value : T) (out : alloc.vec.Vec T)
    (h : batched_weights.filled copyInst n value = .ok (.Ok out)) :
    out.length = n.val := by
  unfold batched_weights.filled at h
  cases htry : alloc.vec.Vec.try_reserve_exact Global (alloc.vec.Vec.new T) n with
  | fail e => simp [htry] at h
  | div => simp [htry] at h
  | ok pair =>
    rcases pair with ⟨reserve, base⟩
    cases reserve with
    | Err err =>
      simp [htry, core.result.Result.map_err,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,
        batched_weights.filled.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorAllocationError.call_once] at h
    | Ok token =>
      simp only [htry, core.result.Result.map_err, bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch] at h
      change (do
        let out1 ← alloc.vec.Vec.resize copyInst.cloneInst base n value
        ok (core.result.Result.Ok out1)) = .ok (.Ok out) at h
      cases hresize : alloc.vec.Vec.resize copyInst.cloneInst base n value with
      | fail e => simp [hresize] at h
      | div => simp [hresize] at h
      | ok resized =>
        simp only [hresize, bind_tc_ok] at h
        injection h with hout
        injection hout with hout2
        subst out
        exact BatchedWeightsVecResizeLengthGenericV1.resize_success_length
          copyInst.cloneInst base resized n value hresize
#print axioms filled_success_length
end BatchedWeightsFilledLengthGenericV5
