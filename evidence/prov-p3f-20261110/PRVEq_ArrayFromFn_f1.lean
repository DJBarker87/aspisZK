-- PCVF_ item 1: core::array::from_fn versus the gate hand model FIq_Native.array_from_fn_copy.
-- What is proved here (no hypotheses):
--   (a) the gate model erases its Copy witness and its dummy initial value (they cannot influence the result);
--   (b) the gate model is OraclePortStdBuilder.fromFn (kernel-checked in-order, state-threading interpretation);
--   (c) for a closure whose call_mut is pure (state unchanged, value g i) the result is the array of g at the indices 0..N-1.
-- What is NOT provable: the bridge  core.array.from_fn N inst f = array_from_fn_copy N copy inst dummy f.
-- In the original-Aeneas emission core.array.from_fn is an `axiom` (FunsExternal_Template.lean,
-- `@[rust_fun "core::array::from_fn"] axiom core.array.from_fn {T F} (N) (inst : FnMut F Usize T) : F → Result (Array T N)`),
-- which has no defining equation; no equality with any defined constant is derivable. Statement of the needed fact below.
import Aeneas
import RPu_FIq_FromFn
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace PCVF_FromFn

/-- (a) Copy witness and dummy are erased. -/
theorem erased {T F : Type} (N : Usize) (c1 c2 : core.marker.Copy T)
    (fn : core.ops.function.FnMut F Usize T) (d1 d2 : T) (f : F) :
    FIq_Native.array_from_fn_copy N c1 fn d1 f = FIq_Native.array_from_fn_copy N c2 fn d2 f := rfl

/-- (b) The gate model is the kernel-checked in-order builder. -/
theorem is_builder {T F : Type} (N : Usize) (c : core.marker.Copy T)
    (fn : core.ops.function.FnMut F Usize T) (d : T) (f : F) :
    FIq_Native.array_from_fn_copy N c fn d f = AspisR1.OraclePortStdBuilder.fromFn N fn f := rfl

/-- (c) Pure closures: the result is the array of g over 0..N-1. -/
theorem pure_closure {T F : Type} (N : Usize) (c : core.marker.Copy T)
    (fn : core.ops.function.FnMut F Usize T) (d : T) (g : Usize → T)
    (h : ∀ s i, fn.call_mut s i = ok (g i, s)) (f : F) :
    FIq_Native.array_from_fn_copy N c fn d f =
      ok (Aeneas.Std.Array.make N ((AspisR1.OraclePortStdBuilder.indices N).map g) (by simp [AspisR1.OraclePortStdBuilder.indices])) :=
  AspisR1.OraclePortStdBuilder.fromFn_pure N fn g h f

/-- THE NEEDED FACT (not proved, not assumed anywhere in this file): for an implementation `cafn` of the
    emission's axiom `core.array.from_fn`, equality with the gate model at every instantiation used.
    A per-instantiation bridge is this statement specialised to (T, F, N, inst) of a dependant. -/
def FromFnBridge
    (cafn : {T F : Type} → (N : Usize) → core.ops.function.FnMut F Usize T → F → Result (Array T N)) : Prop :=
  ∀ {T F : Type} (N : Usize) (inst : core.ops.function.FnMut F Usize T) (copy : core.marker.Copy T) (dummy : T) (f : F),
    cafn N inst f = FIq_Native.array_from_fn_copy N copy inst dummy f

end PCVF_FromFn

#print axioms PCVF_FromFn.erased
#print axioms PCVF_FromFn.is_builder
#print axioms PCVF_FromFn.pure_closure
