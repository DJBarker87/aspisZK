import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import AspisR156FullFreeze.FunsCore

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR156FullFreeze
noncomputable section
namespace AspisR197CurrentBytes

/-- [aspis_v8_performance_host::bytes]: loop body 0:
    Source: '../relation_callback.rs', lines 71:56-71:129 -/
@[rust_loop_body]
def bytes_loop.body
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  aspis_core.field.QM31)) (b : alloc.vec.Vec Std.U8) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter aspis_core.field.QM31)) × (alloc.vec.Vec Std.U8))
    (alloc.vec.Vec Std.U8))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter aspis_core.field.QM31) iter
  match o with
  | none => ok (done b)
  | some p =>
    let (i, v) := p
    let i1 ← lift (Std.Usize.wrapping_mul i 16#usize)
    let i2 ← lift (Std.Usize.wrapping_mul i 16#usize)
    let i3 ← lift (Std.Usize.wrapping_add i2 16#usize)
    let (s, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) b { start := i1, «end» := i3 }
    let s1 ← aspis_core.field.QM31.write_le_bytes v s
    let b1 := index_mut_back s1
    ok (cont (iter1, b1))

/-- [aspis_v8_performance_host::bytes]: loop 0:
    Source: '../relation_callback.rs', lines 71:56-71:129 -/
@[rust_loop]
def bytes_loop
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  aspis_core.field.QM31)) (b : alloc.vec.Vec Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (iter1, b1) => bytes_loop.body iter1 b1)
    (iter, b)

/-- [aspis_v8_performance_host::bytes]:
    Source: '../relation_callback.rs', lines 71:0-71:131 -/
def bytes
  (v : Slice aspis_core.field.QM31) : Result (alloc.vec.Vec Std.U8) := do
  let i := Slice.len v
  let i1 ← lift (Std.Usize.wrapping_mul i 16#usize)
  let b ← alloc.vec.from_elem core.clone.CloneU8 0#u8 i1
  let i2 ← core.slice.Slice.iter v
  let iter ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter aspis_core.field.QM31) i2
  bytes_loop iter b


#print axioms bytes_loop.body
#print axioms bytes_loop
#print axioms bytes

end AspisR197CurrentBytes
