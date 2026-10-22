import AspisR1SemanticInit28.Types
/-! Ordinary Result::map_err semantics; no extraction template axiom. -/
open Aeneas Aeneas.Std Result
namespace AspisR1SemanticInit28

def core.result.Result.map_err
    {T E F O : Type} (f : core.ops.function.FnOnce O E F)
    (value : core.result.Result T E) (closure : O) : Result (core.result.Result T F) := do
  match value with
  | .Ok v => ok (.Ok v)
  | .Err e =>
    let mapped ← f.call_once closure e
    ok (.Err mapped)
end AspisR1SemanticInit28
