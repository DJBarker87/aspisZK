-- Generated exact declaration slice from the pinned combined from_fn candidate Funs.lean; only header/framing is adapted.
import Aeneas.Std
import Aeneas.Tactic.RustAttributes
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::array_from_fn_copy]: loop 0:
    Source: 'src/lib.rs', lines 27:4-30:5 -/
@[rust_loop]
def array_from_fn_copy_loop
  {T : Type} {T2 : Type} {N : Std.Usize} (coreopsfunctionFnMutT2TupleUsizeTInst
  : core.ops.function.FnMut T2 Std.Usize T) (f : T2) (out : Array T N)
  (i : Std.Usize) :
  Result (Array T N)
  := do
  if i < N
  then
    let (t, f1) ← coreopsfunctionFnMutT2TupleUsizeTInst.call_mut f i
    let a ← Array.update out i t
    let i1 ← i + 1#usize
    array_from_fn_copy_loop coreopsfunctionFnMutT2TupleUsizeTInst f1 a i1
  else ok out
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::array_from_fn_copy]:
    Source: 'src/lib.rs', lines 21:0-32:1 -/
def array_from_fn_copy
  {T : Type} {T2 : Type} (N : Std.Usize) (coremarkerCopyInst : core.marker.Copy
  T) (coreopsfunctionFnMutT2TupleUsizeTInst : core.ops.function.FnMut T2
  Std.Usize T) (init : T) (f : T2) :
  Result (Array T N)
  := do
  let out := Array.repeat N init
  array_from_fn_copy_loop coreopsfunctionFnMutT2TupleUsizeTInst f out 0#usize


end AspisR1SelectedMaskProbe
