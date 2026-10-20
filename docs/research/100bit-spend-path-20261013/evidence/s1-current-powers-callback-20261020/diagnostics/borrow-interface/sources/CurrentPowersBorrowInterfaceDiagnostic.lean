import CurrentPowersCallback
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentPowers
-- Diagnostic only: instantiate the emitted FnMut trait with its exact emitted
-- call_mut and call_once functions. This is expected to fail on the selected
-- library, and is never an imported proof dependency.
def emittedFnMut (mul : field.WideExact → field.WideExact → Result field.WideExact)
    (N : Usize) : core.ops.function.FnMut (weights.powers.closure N) Usize field.WideExact := {
  FnOnceInst := {call_once :=
    weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once mul}
  call_mut := weights.powers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut mul
}
-- Exact emitted parent tuple destructuring with the emitted external template
-- return type. No axiomatized external function is needed to exhibit the mismatch.
def emittedParentShape {N : Usize} (f : Result (Array field.WideExact N)) :
    Result (Array field.WideExact N) := do
  let (a, _) ← f
  ok a
end AspisR1CurrentPowers
