import ProverPin2.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace ProverPin2
namespace RW
noncomputable section

-- block emitted by tool k2 (7271db7e), sha256 9d4dc91826629f7955ddd684d6315546e6d8358523ff211970e765ef164ab7cd, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/constraints_v4.rs', 664, 670]
def aspis_statement.constraints_v4.sparse_eq_weight_step
  (weight : aspis_core.field.QM31) (prefix1 : Std.Usize)
  (prefix_len : Std.Usize) (coordinate : Std.Usize)
  (value : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  let i ← lift (Std.Usize.wrapping_sub prefix_len 1#usize)
  let i1 ← lift (Std.Usize.wrapping_sub i coordinate)
  let i2 ← lift (Std.Usize.wrapping_shr prefix1 (UScalar.cast .U32 i1))
  let bit ← lift (i2 &&& 1#usize)
  let value1 ←
    if bit = 0#usize
    then aspis_core.field.QM31.sub aspis_core.field.QM31.ONE value
    else ok value
  aspis_core.field.QM31.mul weight value1

-- block emitted by tool k2 (7271db7e), sha256 10a297288d490f08ee4775dca4b96b4c540e7dba5b7b6f415396520a0fedbc38, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/constraints_v4.rs', 653, 656]
def aspis_statement.constraints_v4.sparse_eq_prefix_weight_loop.body
  (point : Array aspis_core.field.QM31 10#usize) (prefix1 : Std.Usize)
  (prefix_len : Std.Usize) (weight : aspis_core.field.QM31)
  (coordinate : Std.Usize) :
  Result (ControlFlow (aspis_core.field.QM31 × Std.Usize)
    aspis_core.field.QM31)
  := do
  if coordinate < prefix_len
  then
    let q ← Array.index_usize point coordinate
    let weight1 ←
      aspis_statement.constraints_v4.sparse_eq_weight_step weight prefix1
        prefix_len coordinate q
    let coordinate1 ← lift (Std.Usize.wrapping_add coordinate 1#usize)
    ok (cont (weight1, coordinate1))
  else ok (done weight)

-- block emitted by tool k2 (7271db7e), sha256 ffb7176737f7885ac085063b80cc8b746e45d711d9d1d0771d0e425ed080e630, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/constraints_v4.rs', 653, 656]
def aspis_statement.constraints_v4.sparse_eq_prefix_weight_loop
  (point : Array aspis_core.field.QM31 10#usize) (prefix1 : Std.Usize)
  (prefix_len : Std.Usize) (weight : aspis_core.field.QM31)
  (coordinate : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  loop
    (fun (weight1, coordinate1) =>
      aspis_statement.constraints_v4.sparse_eq_prefix_weight_loop.body point
      prefix1 prefix_len weight1 coordinate1)
    (weight, coordinate)

-- block emitted by tool k2 (7271db7e), sha256 6b94eb2b9b3b6ad48e326b2b5c8a75f7c9201cf0123a2e7e6421c1512d007e07, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/constraints_v4.rs', 650, 650]
def aspis_statement.constraints_v4.sparse_eq_prefix_weight
  (point : Array aspis_core.field.QM31 10#usize) (prefix1 : Std.Usize)
  (prefix_len : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  aspis_statement.constraints_v4.sparse_eq_prefix_weight_loop point prefix1
    prefix_len aspis_core.field.QM31.ONE 0#usize

-- block emitted by tool k2 (7271db7e), sha256 fb1a4ae2cdf28fe269e4ad288741e3e0c94aa90657ef6f1dbdd8d71120849869, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/constraints_v4.rs', 636, 641]
def aspis_statement.constraints_v4.sparse_eq_weight_rows_loop.body
  (point : Array aspis_core.field.QM31 10#usize) (prefix_len : Std.Usize)
  (trailing_boolean : Std.Usize) (suffix : Std.Usize) (count : Std.Usize)
  (weights : alloc.vec.Vec (Std.Usize × aspis_core.field.QM31))
  (prefix1 : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec (Std.Usize × aspis_core.field.QM31)) ×
    Std.Usize) (alloc.vec.Vec (Std.Usize × aspis_core.field.QM31)))
  := do
  if prefix1 < count
  then
    let i ←
      lift (Std.Usize.wrapping_shl prefix1 (UScalar.cast .U32
        trailing_boolean))
    let row ← lift (i ||| suffix)
    let weight ←
      aspis_statement.constraints_v4.sparse_eq_prefix_weight point prefix1
        prefix_len
    let weights1 ← alloc.vec.Vec.push weights (row, weight)
    let prefix2 ← lift (Std.Usize.wrapping_add prefix1 1#usize)
    ok (cont (weights1, prefix2))
  else ok (done weights)

-- block emitted by tool k2 (7271db7e), sha256 73163ff06b24c1154c32a868325093bbbd63978d7fa53423f92d78292c63588a, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/constraints_v4.rs', 636, 641]
def aspis_statement.constraints_v4.sparse_eq_weight_rows_loop
  (point : Array aspis_core.field.QM31 10#usize) (prefix_len : Std.Usize)
  (trailing_boolean : Std.Usize) (suffix : Std.Usize) (count : Std.Usize)
  (weights : alloc.vec.Vec (Std.Usize × aspis_core.field.QM31))
  (prefix1 : Std.Usize) :
  Result (alloc.vec.Vec (Std.Usize × aspis_core.field.QM31))
  := do
  loop
    (fun (weights1, prefix2) =>
      aspis_statement.constraints_v4.sparse_eq_weight_rows_loop.body point
      prefix_len trailing_boolean suffix count weights1 prefix2)
    (weights, prefix1)

-- block emitted by tool k2 (7271db7e), sha256 94301946219584a67d3271ed2839a42196bea98379e3f0a036ec35884ce9e939, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/constraints_v4.rs', 627, 632]
def aspis_statement.constraints_v4.sparse_eq_weight_rows
  (point : Array aspis_core.field.QM31 10#usize) (prefix_len : Std.Usize)
  (trailing_boolean : Std.Usize) (suffix : Std.Usize) :
  Result (alloc.vec.Vec (Std.Usize × aspis_core.field.QM31))
  := do
  let count ←
    lift (Std.Usize.wrapping_shl 1#usize (UScalar.cast .U32 prefix_len))
  let weights :=
    alloc.vec.Vec.with_capacity (Std.Usize × aspis_core.field.QM31) count
  aspis_statement.constraints_v4.sparse_eq_weight_rows_loop point prefix_len
    trailing_boolean suffix count weights 0#usize

-- block emitted by tool k2 (7271db7e), sha256 8ff2626fb7404a01061220c5235d6e7633bf8fe46b112b83861584994a1eda1b, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/constraints_v4.rs', 0, 611]
def aspis_statement.constraints_v4.sparse_eq_weights_loop.body
  (iter : core.slice.iter.Iter aspis_core.field.QM31) (suffix : Std.Usize) :
  Result (ControlFlow ((core.slice.iter.Iter aspis_core.field.QM31) ×
    Std.Usize) Std.Usize)
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done suffix)
  | some coordinate =>
    let i ← lift (Std.Usize.wrapping_shl suffix (IScalar.hcast .U32 1#i32))
    let b ←
      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq coordinate
        aspis_core.field.QM31.ONE
    let i1 ← lift (core.convert.num.FromUsizeBool.from b)
    let suffix1 ← lift (i ||| i1)
    ok (cont (iter1, suffix1))

-- block emitted by tool k2 (7271db7e), sha256 91cfb08eee43fd0bef32a37af807e09a76d325a67b4027e614355d2d946be9d8, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/constraints_v4.rs', 0, 611]
def aspis_statement.constraints_v4.sparse_eq_weights_loop
  (iter : core.slice.iter.Iter aspis_core.field.QM31) (suffix : Std.Usize) :
  Result Std.Usize
  := do
  loop
    (fun (iter1, suffix1) =>
      aspis_statement.constraints_v4.sparse_eq_weights_loop.body iter1 suffix1)
    (iter, suffix)

-- block emitted by tool k2 (7271db7e), sha256 80af0cc9f64d8835bc04fb2dad10c839647e6fbc94b90a0f95f4026db58ccac7, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/constraints_v4.rs', 601, 601]
def aspis_statement.constraints_v4.sparse_eq_weights
  (point : Array aspis_core.field.QM31 10#usize) :
  Result (alloc.vec.Vec (Std.Usize × aspis_core.field.QM31))
  := do
  let s ← lift (Array.to_slice point)
  let i ← core.slice.Slice.iter s
  let r ←
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorSliceIter aspis_core.field.QM31)
      (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
      aspis_core.field.QM31) i
  let tw ←
    core.iter.traits.iterator.Iterator.take_while.default
      (core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator
      (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
      aspis_core.field.QM31))
      aspis_statement.constraints_v4.sparse_eq_weights.closure.Insts.CoreOpsFunctionFnMutTupleSharedSharedQM31Bool
      r ()
  let trailing_boolean ←
    core.iter.traits.iterator.Iterator.count.default
      (core.iter.adapters.take_while.TakeWhile.Insts.CoreIterTraitsIteratorIterator
      (core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator
      (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
      aspis_core.field.QM31))
      aspis_statement.constraints_v4.sparse_eq_weights.closure.Insts.CoreOpsFunctionFnMutTupleSharedSharedQM31Bool)
      tw
  let s1 ← lift (Array.to_slice point)
  let i1 := Slice.len s1
  let prefix_len ← lift (Std.Usize.wrapping_sub i1 trailing_boolean)
  let s2 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice aspis_core.field.QM31))
      point { start := prefix_len }
  let iter ←
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter s2
  let suffix ←
    aspis_statement.constraints_v4.sparse_eq_weights_loop iter 0#usize
  aspis_statement.constraints_v4.sparse_eq_weight_rows point prefix_len
    trailing_boolean suffix

end
end RW
end ProverPin2

#check @ProverPin2.RW.aspis_statement.constraints_v4.sparse_eq_weight_step
#print axioms ProverPin2.RW.aspis_statement.constraints_v4.sparse_eq_weight_step
#check @ProverPin2.RW.aspis_statement.constraints_v4.sparse_eq_prefix_weight
#print axioms ProverPin2.RW.aspis_statement.constraints_v4.sparse_eq_prefix_weight
#check @ProverPin2.RW.aspis_statement.constraints_v4.sparse_eq_weight_rows
#print axioms ProverPin2.RW.aspis_statement.constraints_v4.sparse_eq_weight_rows
example : type_of% @ProverPin2.RW.aspis_statement.constraints_v4.sparse_eq_weights = type_of% @ProverPin2.aspis_statement.constraints_v4.sparse_eq_weights := rfl
#check @ProverPin2.RW.aspis_statement.constraints_v4.sparse_eq_weights
#print axioms ProverPin2.RW.aspis_statement.constraints_v4.sparse_eq_weights
-- 10 carried blocks, 0 new opaque items, 1 signature checks
