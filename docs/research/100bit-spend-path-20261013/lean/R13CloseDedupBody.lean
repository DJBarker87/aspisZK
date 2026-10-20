import R13CloseLoop
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2.R13Close.Dedup
abbrev Idx := Array U32 16#usize
abbrev Val := Array (Array U8 32#usize) 16#usize
abbrev Leaf := Array U8 32#usize

def verifier.candidate.same_batch_leaf
  (values : Array (Array Std.U8 32#usize) 16#usize) (index : Std.Usize)
  (leaf : Array Std.U8 32#usize) :
  Result Bool
  := do
  let a ← Array.index_usize values index
  core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a leaf

def verifier.candidate.same_batch_index
  (values : Array Std.U32 16#usize) (index : Std.Usize) (expected : Std.U32) :
  Result Bool
  := do
  let i ← Array.index_usize values index
  ok (i = expected)

def dedupStep (idx : Idx) (val : Val) (d key_position1 : Usize)
    (index : U32) (leaf : Leaf) :
    Result (ControlFlow (Idx × Val × Usize × Usize)
      (Idx × Val × Option (core.result.Result Unit verifier.Error))) := do
    if d > 0#usize
    then
      let i4 ← d - 1#usize
      let b ← verifier.candidate.same_batch_index idx i4 index
      if b
      then
        let b1 ← verifier.candidate.same_batch_leaf val i4 leaf
        if b1
        then ok (cont (idx, val, d, key_position1))
        else
          ok (done (idx, val, some (core.result.Result.Err
            verifier.Error.Merkle)))
      else
        let idx1 ← Array.update idx d index
        let val1 ← Array.update val d leaf
        let d1 ← d + 1#usize
        ok (cont (idx1, val1, d1, key_position1))
    else
      let idx1 ← Array.update idx d index
      let val1 ← Array.update val d leaf
      let d1 ← d + 1#usize
      ok (cont (idx1, val1, d1, key_position1))

end AspisR1Stage2.R13Close.Dedup
