-- PCVF_ item 5 (Option/Result helper class) / item 4 (Option.ok_or, S1NativeCompactModelV1).
-- Fresh text: PCQD_d04 emission (prov-p1g-20261109/PCQD_E013_emitted/raw/PCQD_d04, original Aeneas 959659a6, overflow ON), declaration core.option.Option.ok_or.
-- Statement is fresh = gate against the compiled gate constant AspisS1NativeCompact.core.option.Option.ok_or.
import Aeneas
import S1NativeCompactModelV1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisS1NativeCompact
namespace PRVFresh_S1NativeCompactModelV1

def core.option.Option.ok_or
  {T : Type} {E : Type} (self : Option T) (err : E) :
  Result (core.result.Result T E)
  := do
  match self with
  | none => ok (core.result.Result.Err err)
  | some v => ok (core.result.Result.Ok v)

end PRVFresh_S1NativeCompactModelV1
end AspisS1NativeCompact

theorem PRVEq.S1NativeCompactModelV1.core.option.Option.ok_or_f1 :
    @AspisS1NativeCompact.PRVFresh_S1NativeCompactModelV1.core.option.Option.ok_or =
    @AspisS1NativeCompact.core.option.Option.ok_or := by
  funext T E self err
  cases self <;> rfl
#print axioms PRVEq.S1NativeCompactModelV1.core.option.Option.ok_or_f1
