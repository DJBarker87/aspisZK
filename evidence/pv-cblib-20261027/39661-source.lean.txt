-- Generic copy kernel retained verbatim from the successful Aeneas extraction.
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBL_ArrayKernel
/-- [pv_cblib_source::array_reference]: loop body 0:
    Source: 'lib.rs', lines 38:4-38:36
    Visibility: public -/
@[rust_loop_body]
def array_reference_loop.body
  {T : Type} {N : Std.Usize} (v : Slice T) (out : Array T N) (i : Std.Usize) :
  Result (ControlFlow ((Array T N) × Std.Usize) (Array T N))
  := do
  if i < N
  then
    let t ← Slice.index_usize v i
    let out1 ← Array.update out i t
    let i1 ← lift (Std.Usize.wrapping_add i 1#usize)
    ok (cont (out1, i1))
  else ok (done out)

/-- [pv_cblib_source::array_reference]: loop 0:
    Source: 'lib.rs', lines 38:4-38:36
    Visibility: public -/
@[rust_loop]
def array_reference_loop
  {T : Type} {N : Std.Usize} (v : Slice T) (out : Array T N) (i : Std.Usize) :
  Result (Array T N)
  := do
  loop
    (fun (out1, i1) => array_reference_loop.body v out1 i1)
    (out, i)

/-- [pv_cblib_source::array_reference]:
    Source: 'lib.rs', lines 34:0-40:1
    Visibility: public -/
def array_reference
  {T : Type} (N : Std.Usize) (coremarkerCopyInst : core.marker.Copy T)
  (v : Slice T) (zero : T) :
  Result (Option (Array T N))
  := do
  let i := Slice.len v
  if i != N
  then ok none
  else
    let out := Array.repeat N zero
    let out1 ← array_reference_loop v out 0#usize
    ok (some out1)


#print axioms array_reference_loop.body
#print axioms array_reference_loop
#print axioms array_reference
end PV_CBL_ArrayKernel
