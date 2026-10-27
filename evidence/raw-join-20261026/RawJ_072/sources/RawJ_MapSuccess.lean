import S1CurrentPrepareCodeV1
set_option autoImplicit false
namespace AspisR1.RawJ_MapSuccess
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

theorem semantic {H : Type} (D : aspis_core.digest.Digest32 H)
    (r : core.result.Result (r1_semantic.Verified H) r1_wire.Error)
    (mapped : core.result.Result (r1_semantic.Verified H) verifier.Error)
    (value : r1_semantic.Verified H)
    (hm : core.result.Result.map_err
      (verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError D) r () = ok mapped)
    (hc : core.result.Result.Insts.CoreOpsTry.branch mapped = ok (.Continue value)) : r = .Ok value := by
  cases r with
  | Ok a =>
    simp only [core.result.Result.map_err] at hm
    cases Result.ok.inj hm
    simpa only [core.result.Result.Insts.CoreOpsTry.branch,Result.ok.injEq,
      core.ops.control_flow.ControlFlow.Continue.injEq] using congrArg core.result.Result.Ok hc
  | Err e =>
    unfold core.result.Result.map_err at hm
    repeat' first
      | (solve | cases hm)
      | (solve | cases hc)
      | uncase_result
      | head_reduce hm
      | head_reduce hc
      | split at hm

#print axioms semantic
end AspisR1.RawJ_MapSuccess
