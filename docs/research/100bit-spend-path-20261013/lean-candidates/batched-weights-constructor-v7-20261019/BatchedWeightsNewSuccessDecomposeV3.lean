import AspisR1BatchedWeightsExtraction.Funs
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1BatchedWeightsExtraction
namespace BatchedWeightsNewSuccessDecomposeV3

theorem new_success_decompose (weights : Slice aspis_core.field.QM31)
    (state : batched_weights.BatchedWeights)
    (h : batched_weights.BatchedWeights.new weights = .ok (.Ok state)) :
    ∃ rawInit rawOut,
      batched_weights.filled
        (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64)
        (Slice.len weights) (Array.repeat 4#usize 0#u64) = .ok (.Ok rawInit) ∧
      batched_weights.BatchedWeights.new_loop
        { start := 0#usize, «end» := Slice.len weights } weights rawInit = .ok rawOut ∧
      state = { raw := rawOut, terms := 0#usize } := by
  unfold batched_weights.BatchedWeights.new at h
  cases hf : batched_weights.filled
      (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64)
      (Slice.len weights) (Array.repeat 4#usize 0#u64) with
  | fail e => simp [hf] at h
  | div => simp [hf] at h
  | ok r =>
    cases r with
    | Err e =>
      simp [hf, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at h
    | Ok rawInit =>
      simp only [hf, bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch] at h
      cases hloop : batched_weights.BatchedWeights.new_loop
          { start := 0#usize, «end» := Slice.len weights } weights rawInit with
      | fail e => simp [hloop] at h
      | div => simp [hloop] at h
      | ok rawOut =>
        simp only [hloop, bind_tc_ok] at h
        have hstate : { raw := rawOut, terms := 0#usize } = state := by
          injection h with hres
          injection hres
        exact ⟨rawInit, rawOut, rfl, hloop, hstate.symm⟩
#print axioms new_success_decompose
end BatchedWeightsNewSuccessDecomposeV3
