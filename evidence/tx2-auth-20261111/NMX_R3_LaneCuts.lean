import NCV_Reference.Funs
set_option autoImplicit false
namespace NMX_R3_LaneCuts
open Aeneas Aeneas.Std Result NCV_Reference

def finish (b : Slice U8) (master : Array U8 32#usize) (i2 : U8) (next_leaf_index : U64) (val : Array U32 8#usize) (val1 : Array (Array U32 8#usize) 20#usize) : Result (core.result.Result NCV_Reference.Lane Unit) := do
  if next_leaf_index = 0#u64
  then
    let a ←
      Array.index_usize NCV_Reference.EMPTY 20#usize
    let b6 ← NCV_Reference.eq_digest val a
    if b6
    then
      let i9 ← Slice.index_usize b 72#usize
      ok (core.result.Result.Ok
        {
          bump := i9,
          master,
          lane_id := i2,
          next_leaf_index,
          root := val,
          frontier := val1
        })
    else ok (core.result.Result.Err ())
  else
    let i9 ← Slice.index_usize b 72#usize
    ok (core.result.Result.Ok
      {
        bump := i9,
        master,
        lane_id := i2,
        next_leaf_index,
        root := val,
        frontier := val1
      })

def frontier (b : Slice U8) (master : Array U8 32#usize) (i2 : U8) (tree : Slice U8) (next_leaf_index : U64) (val : Array U32 8#usize) : Result (core.result.Result NCV_Reference.Lane Unit) := do
  let r1 ←
    NCV_Reference.decode_frontier tree next_leaf_index
  let cf1 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r1
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue
    val1 =>
    NMX_R3_LaneCuts.finish b master i2 next_leaf_index val val1
  | core.ops.control_flow.ControlFlow.Break
    residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Lane (core.convert.FromSame Unit)
      residual

def digest (b : Slice U8) (master : Array U8 32#usize) (i2 : U8) (tree : Slice U8) (next_leaf_index : U64) : Result (core.result.Result NCV_Reference.Lane Unit) := do
  let r ← NCV_Reference.digest tree 16#usize
  let cf ←
    core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue
    val =>
    NMX_R3_LaneCuts.frontier b master i2 tree next_leaf_index val
  | core.ops.control_flow.ControlFlow.Break
    residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Lane (core.convert.FromSame Unit) residual

def counter (b : Slice U8) (master : Array U8 32#usize) (i2 : U8) (tree : Slice U8) : Result (core.result.Result NCV_Reference.Lane Unit) := do
  let next_leaf_index ← NCV_Reference.word64 tree 8#usize
  if next_leaf_index > 1048576#u64
  then ok (core.result.Result.Err ())
  else
    NMX_R3_LaneCuts.digest b master i2 tree next_leaf_index

def tree (b : Slice U8) (master : Array U8 32#usize) (i2 : U8) : Result (core.result.Result NCV_Reference.Lane Unit) := do
  let tree ←
    core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)
      b { start := 80#usize }
  let s6 ←
    core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)
      tree { «end» := 4#usize }
  let s7 ←
    lift (Array.to_slice
      (Array.make 4#usize [ 65#u8, 83#u8, 80#u8, 84#u8 ]))
  let b5 ← NCV_Reference.equal s6 s7
  if b5
  then
    let i5 ← Slice.index_usize tree 4#usize
    if i5 != 1#u8
    then ok (core.result.Result.Err ())
    else
      let i6 ← Slice.index_usize tree 5#usize
      if i6 != 20#u8
      then ok (core.result.Result.Err ())
      else
        let i7 ← Slice.index_usize tree 6#usize
        if i7 != 3#u8
        then ok (core.result.Result.Err ())
        else
          let i8 ← Slice.index_usize tree 7#usize
          if i8 != 1#u8
          then ok (core.result.Result.Err ())
          else
            NMX_R3_LaneCuts.counter b master i2 tree
  else ok (core.result.Result.Err ())

def master (b : Slice U8) (i2 : U8) : Result (core.result.Result NCV_Reference.Lane Unit) := do
  let master ← NCV_Reference.bytes32 b 40#usize
  let s5 ← lift (Array.to_slice master)
  let b4 ← NCV_Reference.zero s5
  if b4
  then ok (core.result.Result.Err ())
  else
    NMX_R3_LaneCuts.tree b master i2

def header (b : Slice U8) : Result (core.result.Result NCV_Reference.Lane Unit) := do
  let s ←
    core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) b
      { «end» := 4#usize }
  let s1 ←
    lift (Array.to_slice (Array.make 4#usize [ 65#u8, 83#u8, 76#u8, 56#u8 ]))
  let b1 ← NCV_Reference.equal s s1
  if b1
  then
    let i1 ← Slice.index_usize b 4#usize
    if i1 != 2#u8
    then ok (core.result.Result.Err ())
    else
      let i2 ← Slice.index_usize b 5#usize
      if i2 >= 8#u8
      then ok (core.result.Result.Err ())
      else
        let i3 ← Slice.index_usize b 6#usize
        if i3 != 8#u8
        then ok (core.result.Result.Err ())
        else
          let i4 ← Slice.index_usize b 7#usize
          if i4 != 20#u8
          then ok (core.result.Result.Err ())
          else
            let s2 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
                { start := 8#usize, «end» := 40#usize }
            let s3 ← lift (Array.to_slice BINDING)
            let b2 ← NCV_Reference.equal s2 s3
            if b2
            then
              let s4 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b
                  { start := 73#usize, «end» := 80#usize }
              let b3 ← NCV_Reference.zero s4
              if b3
              then
                NMX_R3_LaneCuts.master b i2
              else ok (core.result.Result.Err ())
            else ok (core.result.Result.Err ())
  else ok (core.result.Result.Err ())

def run (b : Slice U8) : Result (core.result.Result NCV_Reference.Lane Unit) := do

  let i := Slice.len b
  if i != 768#usize
  then ok (core.result.Result.Err ())
  else
    NMX_R3_LaneCuts.header b

theorem factor (b : Slice U8) : run b = NCV_Reference.decode_lane_ref b := by
 rfl
#print axioms factor
end NMX_R3_LaneCuts
