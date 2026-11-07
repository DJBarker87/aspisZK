import NMP_prepare.Funs
import NMT_CallTree
set_option autoImplicit false
namespace AspisR1.NMP_StdMapErr
open Aeneas Aeneas.Std Result NMP_prepare
/-- Complete std Result::map_err law: only Err invokes its actual callback. -/
def run {T E F O : Type} (inst : core.ops.function.FnOnce O E F)
 (r : core.result.Result T E) (o : O) : Result (core.result.Result T F) :=
 match r with
 | .Ok value => .ok (.Ok value)
 | .Err error => do let mapped ← inst.call_once o error; .ok (.Err mapped)
theorem ok {T E F O : Type} (inst : core.ops.function.FnOnce O E F) (v : T) (o : O) :
 run inst (.Ok v) o = .ok (.Ok v) := rfl
theorem err {T E F O : Type} (inst : core.ops.function.FnOnce O E F) (e : E) (o : O) :
 run inst (.Err e) o = (do let mapped ← inst.call_once o e; .ok (.Err mapped)) := rfl
/-- The actual emitted allocation callback ignores every r0 error payload. -/
theorem allocation {H : Type} (d : aspis_core.digest.Digest32 H) (e : aspis_core.r0.Error) :
 verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once d () e = .ok verifier.Error.Allocation := rfl
/-- The actual emitted semantic callback ignores every wire error payload;
there is no String-error clone or synthetic allocation at this site. -/
theorem semantic {H : Type} (d : aspis_core.digest.Digest32 H) (e : r1_wire.Error) :
 verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once d () e = .ok verifier.Error.Semantic := rfl
#print axioms ok
#print axioms err
#print axioms allocation
#print axioms semantic
end AspisR1.NMP_StdMapErr
