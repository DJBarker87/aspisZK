import AspisR1SimSemantic20.Funs
/-! Complete extracted fueled validator; all reused field dependencies have
identical bodies in the retained namespace. No opaque cut or template axiom. -/
namespace AspisR1SimSemantic20
open Aeneas Aeneas.Std Result
def r1_wire.fields29.finite
  (row : Std.U8) (payload : alloc.vec.Vec Std.U8) (value : Std.Usize)
  (remaining : Std.Usize) :
  Result (core.result.Result Unit r1_wire.Error)
  := do
  if remaining = 0#usize
  then ok (core.result.Result.Ok ())
  else
    let i := alloc.vec.Vec.len payload
    if i < 32#usize
    then ok (core.result.Result.Ok ())
    else
      let bytes ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice
          Std.U8) payload { «end» := 32#usize }
      let o ← aspis_core.field.wide_exact.WideExact.from_le_bytes bytes
      match o with
      | none =>
        ok (core.result.Result.Err (r1_wire.Error.NonCanonical row value))
      | some x =>
        let q ← aspis_core.field.wide_exact.WideExact.impl.c1 x
        let b ←
          core.cmp.PartialEq.ne.trait_default
            aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 q
            aspis_core.field.QM31.ZERO
        if b
        then ok (core.result.Result.Err (r1_wire.Error.NonCanonical row value))
        else
          let s ←
            alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice
              Std.U8) payload { start := 32#usize }
          let tail ← alloc.slice.Slice.to_vec core.clone.CloneU8 s
          let i1 ← lift (core.num.Usize.wrapping_add value 1#usize)
          let i2 ← lift (core.num.Usize.wrapping_sub remaining 1#usize)
          r1_wire.fields29.finite row tail i1 i2
partial_fixpoint

end AspisR1SimSemantic20
