import R1Z.PV_Src_CompilerTactic
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ResultMap31
open Aeneas Aeneas.Std Result

theorem success {α ε ζ C : Type} (f : core.ops.function.FnOnce C ε ζ)
    (r : core.result.Result α ε) (c : C) (a : α)
    (h : BuilderForestStdPort.core.result.Result.map_err f r c = ok (.Ok a)) :
    r = .Ok a := by
  cases r with
  | Ok x =>
    change (ok (.Ok x) : Result (core.result.Result α ζ)) = ok (.Ok a) at h
    cases h
    rfl
  | Err error =>
    unfold BuilderForestStdPort.core.result.Result.map_err BuilderAdmissionStd.mapErr at h
    pv_peel h with mapped hm
    cases h
#print axioms success
end R1Z.PV_RunJoin_ResultMap31
