import Aeneas

open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBL_JoinSlices
def join_slices_reference
  (base : Slice Std.U8) (path : Slice Std.U8) (out : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let i := Slice.len path
  if i > 0#usize
  then
    let i1 ← Slice.index_usize path 0#usize
    if i1 = 47#u8
    then alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out path
    else
      let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out base
      let i2 := Slice.len base
      let out2 ←
        if i2 > 0#usize
        then
          do
          let i3 := Slice.len base
          let i4 ← lift (Std.Usize.wrapping_sub i3 1#usize)
          let i5 ← Slice.index_usize base i4
          if i5 != 47#u8
          then alloc.vec.Vec.push out1 47#u8
          else ok out1
        else ok out1
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out2 path
  else
    let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out base
    let i1 := Slice.len base
    let out2 ←
      if i1 > 0#usize
      then
        do
        let i2 := Slice.len base
        let i3 ← lift (Std.Usize.wrapping_sub i2 1#usize)
        let i4 ← Slice.index_usize base i3
        if i4 != 47#u8
        then alloc.vec.Vec.push out1 47#u8
        else ok out1
      else ok out1
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out2 path

#print axioms join_slices_reference
end PV_CBL_JoinSlices
