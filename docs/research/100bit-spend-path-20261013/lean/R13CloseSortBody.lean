import R13CloseLoop
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2.R13Close.Sort

def verifier.candidate.batch_key_at
  (keys : Array Std.U64 16#usize) (index : Std.Usize) : Result Std.U64 := do
  Array.index_usize keys index

def verifier.candidate.sort_batch_keys_loop0_loop0.body
  (keys : Array Std.U64 16#usize) (j : Std.Usize) :
  Result (ControlFlow ((Array Std.U64 16#usize) × Std.Usize) (Array Std.U64
    16#usize))
  := do
  if j > 0#usize
  then
    let i ← j - 1#usize
    let i1 ← verifier.candidate.batch_key_at keys i
    let i2 ← verifier.candidate.batch_key_at keys j
    if i1 > i2
    then
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut keys)
      let s1 ← core.slice.Slice.swap s i j
      let keys1 := to_slice_mut_back s1
      ok (cont (keys1, i))
    else ok (done keys)
  else ok (done keys)

def verifier.candidate.sort_batch_keys_loop0_loop0
  (keys : Array Std.U64 16#usize) (j : Std.Usize) :
  Result (Array Std.U64 16#usize)
  := do
  loop
    (fun (keys1, j1) => verifier.candidate.sort_batch_keys_loop0_loop0.body
      keys1 j1)
    (keys, j)

def verifier.candidate.sort_batch_keys_loop0.body
  (iter : core.ops.range.Range Std.Usize) (keys : Array Std.U64 16#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U64
    16#usize)) (Array Std.U64 16#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done keys)
  | some i =>
    let keys1 ← verifier.candidate.sort_batch_keys_loop0_loop0 keys i
    ok (cont (iter1, keys1))

def verifier.candidate.sort_batch_keys_loop0
  (iter : core.ops.range.Range Std.Usize) (keys : Array Std.U64 16#usize) :
  Result (Array Std.U64 16#usize)
  := do
  loop
    (fun (iter1, keys1) => verifier.candidate.sort_batch_keys_loop0.body iter1
      keys1)
    (iter, keys)

def verifier.candidate.sort_batch_keys
  (keys : Array Std.U64 16#usize) (n : Std.Usize) :
  Result (Array Std.U64 16#usize)
  := do
  verifier.candidate.sort_batch_keys_loop0 { start := 1#usize, «end» := n }
    keys

end AspisR1Stage2.R13Close.Sort
