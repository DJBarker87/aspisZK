import NJA_Small
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace NJA_Multiproof
variable (NJA_well_formed : Slice U32 → Result Bool)
/-- [aspis_r1_cost_probe::multiproof::node_count]: loop body 2:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 99:12-101:13
    Visibility: public -/
@[rust_loop_body]
def multiproof.node_count_loop0_loop0_loop0.body
  (arity : multiproof.Arity) (level : Array Std.U32 16#usize) (n : Std.Usize)
  (parent : Std.U32) (j : Std.Usize) :
  Result (ControlFlow Std.Usize Std.Usize)
  := do
  if j < n
  then
    let i ← multiproof.index_at level j
    let i1 ← multiproof.Arity.bits arity
    let i2 ← lift (Std.U32.wrapping_shr i i1)
    if i2 = parent
    then let j1 ← lift (Std.Usize.wrapping_add j 1#usize)
         ok (cont j1)
    else ok (done j)
  else ok (done j)

/-- [aspis_r1_cost_probe::multiproof::node_count]: loop 2:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 99:12-101:13
    Visibility: public -/
@[rust_loop]
def multiproof.node_count_loop0_loop0_loop0
  (arity : multiproof.Arity) (level : Array Std.U32 16#usize) (n : Std.Usize)
  (parent : Std.U32) (j : Std.Usize) :
  Result Std.Usize
  := do
  loop
    (fun j1 => multiproof.node_count_loop0_loop0_loop0.body arity level n
      parent j1)
    j

/-- [aspis_r1_cost_probe::multiproof::node_count]: loop body 1:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 96:8-106:9
    Visibility: public -/
@[rust_loop_body]
def multiproof.node_count_loop0_loop0.body
  (arity : multiproof.Arity) (n : Std.Usize) (level : Array Std.U32 16#usize)
  (count : Std.Usize) (w : Std.Usize) (i : Std.Usize) :
  Result (ControlFlow ((Array Std.U32 16#usize) × Std.Usize × Std.Usize ×
    Std.Usize) ((Array Std.U32 16#usize) × Std.Usize × Std.Usize))
  := do
  if i < n
  then
    let i1 ← multiproof.index_at level i
    let i2 ← multiproof.Arity.bits arity
    let parent ← lift (Std.U32.wrapping_shr i1 i2)
    let j ← multiproof.node_count_loop0_loop0_loop0 arity level n parent i
    let i3 ← multiproof.Arity.width arity
    let i4 ← lift (Std.Usize.wrapping_sub j i)
    let i5 ← lift (Std.Usize.wrapping_sub i3 i4)
    let count1 ← lift (Std.Usize.wrapping_add count i5)
    let level1 ← Array.update level w parent
    let w1 ← lift (Std.Usize.wrapping_add w 1#usize)
    ok (cont (level1, count1, w1, j))
  else ok (done (level, count, w))

/-- [aspis_r1_cost_probe::multiproof::node_count]: loop 1:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 96:8-106:9
    Visibility: public -/
@[rust_loop]
def multiproof.node_count_loop0_loop0
  (arity : multiproof.Arity) (level : Array Std.U32 16#usize) (n : Std.Usize)
  (count : Std.Usize) (w : Std.Usize) (i : Std.Usize) :
  Result ((Array Std.U32 16#usize) × Std.Usize × Std.Usize)
  := do
  loop
    (fun (level1, count1, w1, i1) => multiproof.node_count_loop0_loop0.body
      arity n level1 count1 w1 i1)
    (level, count, w, i)

/-- [aspis_r1_cost_probe::multiproof::node_count]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 93:4-108:5
    Visibility: public -/
@[rust_loop_body]
def multiproof.node_count_loop0.body
  (arity : multiproof.Arity) (iter : core.ops.range.Range Std.U32)
  (level : Array Std.U32 16#usize) (n : Std.Usize) (count : Std.Usize) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (Array Std.U32
    16#usize) × Std.Usize × Std.Usize) Std.Usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done count)
  | some _ =>
    let (level1, count1, w) ←
      multiproof.node_count_loop0_loop0 arity level n count 0#usize 0#usize
    ok (cont (iter1, level1, w, count1))

/-- [aspis_r1_cost_probe::multiproof::node_count]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 93:4-108:5
    Visibility: public -/
@[rust_loop]
def multiproof.node_count_loop0
  (iter : core.ops.range.Range Std.U32) (arity : multiproof.Arity)
  (level : Array Std.U32 16#usize) (n : Std.Usize) (count : Std.Usize) :
  Result Std.Usize
  := do
  loop
    (fun (iter1, level1, n1, count1) => multiproof.node_count_loop0.body arity
      iter1 level1 n1 count1)
    (iter, level, n, count)

/-- [aspis_r1_cost_probe::multiproof::node_count]:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 85:0-110:1
    Visibility: public -/
def multiproof.node_count
  (arity : multiproof.Arity) (indices : Slice Std.U32) :
  Result (Option Std.Usize)
  := do
  let b ← NJA_well_formed indices
  if b
  then
    let level := Array.repeat 16#usize 0#u32
    let i := Slice.len indices
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) level
        { «end» := i }
    let s1 ← core.slice.Slice.copy_from_slice core.marker.CopyU32 s indices
    let level1 := index_mut_back s1
    let n := Slice.len indices
    let i1 ← multiproof.Arity.levels arity
    let count ←
      multiproof.node_count_loop0 { start := 0#u32, «end» := i1 } arity
        level1 n 0#usize
    ok (some count)
  else ok none


#print axioms multiproof.node_count
end NJA_Multiproof
