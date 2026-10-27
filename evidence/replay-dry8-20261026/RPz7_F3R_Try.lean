import RPz7_F3R_Result
set_option autoImplicit false
namespace AspisR1.F3R_Try
open Aeneas Aeneas.Std Result

theorem continued {A E : Type} (r : core.result.Result A E) (a : A)
    (call : core.result.Result.Insts.CoreOpsTry.branch r=ok (.Continue a)) : r=.Ok a := by
  cases r with
  | Err e=>cases call
  | Ok v=>simpa only [core.result.Result.Insts.CoreOpsTry.branch,Result.ok.injEq,
      core.ops.control_flow.ControlFlow.Continue.injEq] using congrArg (fun x=>match x with
        | .Continue v=>core.result.Result.Ok v
        | .Break e=>.Err (by cases e with | Err e=>exact e | Ok u=>cases u)) (Result.ok.inj call)

#print axioms continued
end AspisR1.F3R_Try
