import Aeneas

open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBL_PopSlices
def pop_slices_reference_loop.body
  {T : Type} (v : Slice T) (last : Std.Usize) (out : alloc.vec.Vec T)
  (i : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec T) × Std.Usize) (alloc.vec.Vec T))
  := do
  if i < last
  then
    let t ← Slice.index_usize v i
    let out1 ← alloc.vec.Vec.push out t
    let i1 ← lift (Std.Usize.wrapping_add i 1#usize)
    ok (cont (out1, i1))
  else ok (done out)

def pop_slices_reference_loop
  {T : Type} (v : Slice T) (out : alloc.vec.Vec T) (last : Std.Usize)
  (i : Std.Usize) :
  Result (alloc.vec.Vec T)
  := do
  loop
    (fun (out1, i1) => pop_slices_reference_loop.body v last out1 i1)
    (out, i)

def pop_slices_reference
  {T : Type} (coremarkerCopyInst : core.marker.Copy T) (v : Slice T)
  (out : alloc.vec.Vec T) :
  Result ((Option T) × (alloc.vec.Vec T))
  := do
  let i := Slice.len v
  if i = 0#usize
  then ok (none, out)
  else
    let i1 := Slice.len v
    let last ← lift (Std.Usize.wrapping_sub i1 1#usize)
    let out1 ← pop_slices_reference_loop v out last 0#usize
    let t ← Slice.index_usize v last
    ok (some t, out1)

#print axioms pop_slices_reference_loop.body
#print axioms pop_slices_reference_loop
#print axioms pop_slices_reference
end PV_CBL_PopSlices
