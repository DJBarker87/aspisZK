-- PCVI_ item 1: S1NativeCompact expand_semantic, expand_semantic_loop, expand_semantic_loop.body (CONDITIONAL_ON_BINDING).
-- Fresh text: prov-p2d-20261109/inputs/fresh_S1NativeCompactModelV1/Funs.lean (XRn_Join_Release emission of frozen 4bb3b3f, overflow ON).
-- Changes to the emission text, all mechanical: the namespace prefix _root_.XRn_Join_Release. is dropped (names resolve to PRVF);
-- the external compact.expand_values is replaced by a parameter `ext`; CodecError is read as the gate type
-- AspisR1CurrentCaller.compact.CodecError (gate abbrev compact.CodecError; same constructor Length).
-- Statements are fresh = gate against compiled gate constants. Binding (ext = the frozen compact.expand_values) stays at the instantiation.
import Aeneas
import S1NativeCompactModelV1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisS1NativeCompact
namespace PRVF

/-- [aspis_r1_cost_probe::compact::SEMANTIC_COMPACT_VALUES]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 33:0-33:72
    Visibility: public -/
@[global_simps, irreducible]
def compact.SEMANTIC_COMPACT_VALUES : Result Std.Usize := do
  let i ← 10#usize * 28#usize
  let i1 ← 1#usize + i
  let i2 ← 87#usize + 29#usize
  let i3 ← i1 + i2
  i3 + 29#usize

/-- [aspis_r1_cost_probe::verifier::SEMANTIC_BYTES]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 8:0-8:43
    Visibility: public -/
@[global_simps, irreducible]
def verifier.SEMANTIC_BYTES : Result Std.Usize := do
  let i ← 29#usize * 32#usize
  12903#usize + i

/-- [aspis_r1_cost_probe::compact::LOGICAL_SEMANTIC]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 31:0-31:68
    Visibility: public -/
@[global_simps, irreducible]
def compact.LOGICAL_SEMANTIC : Result Std.Usize := verifier.SEMANTIC_BYTES

/-- [aspis_r1_cost_probe::compact::COMPACT_SEMANTIC]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 34:0-34:84
    Visibility: public -/
@[global_simps, irreducible]
def compact.COMPACT_SEMANTIC : Result Std.Usize := do
  let i ← compact.SEMANTIC_COMPACT_VALUES
  let i1 ← 16#usize * i
  let i2 ← compact.LOGICAL_SEMANTIC
  i2 - i1

/-- [aspis_r1_cost_probe::r1_wire::POINTS]
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 14:0-14:28
    Visibility: public -/
@[global_simps, irreducible] def r1_wire.POINTS : Std.Usize := 3#usize

/-- [aspis_r1_cost_probe::r1_wire::LANES]
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 13:0-13:28
    Visibility: public -/
@[global_simps, irreducible] def r1_wire.LANES : Std.Usize := 29#usize

/-- [aspis_r1_cost_probe::r1_wire::CLAIMS]
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 15:0-15:41
    Visibility: public -/
@[global_simps, irreducible]
def r1_wire.CLAIMS : Result Std.Usize := r1_wire.POINTS * r1_wire.LANES

/-- [aspis_r1_cost_probe::r1_wire::row_shape]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 39:0-49:1
    Visibility: public -/
def r1_wire.row_shape
  (row : Std.U8) : Result (Option (Std.U8 × Std.Usize)) := do
  match row with
  | 0#uscalar => ok (some (0#u8, 0#usize))
  | 1#uscalar => ok (some (0#u8, 0#usize))
  | 2#uscalar => ok (some (1#u8, 32#usize))
  | 14#uscalar => ok (some (3#u8, 32#usize))
  | 25#uscalar =>
    let i ← r1_wire.CLAIMS
    let i1 ← i + r1_wire.LANES
    let i2 ← i1 * 32#usize
    ok (some (4#u8, i2))
  | 26#uscalar => let i ← r1_wire.LANES * 32#usize
                  ok (some (5#u8, i))
  | _ =>
    if 3#u8 <= row
    then
      if row <= 13#u8
      then ok (some (0#u8, 0#usize))
      else
        if 15#u8 <= row
        then
          if row <= 24#u8
          then let i ← 28#usize * 32#usize
               ok (some (2#u8, i))
          else ok none
        else ok none
    else
      if 15#u8 <= row
      then
        if row <= 24#u8
        then let i ← 28#usize * 32#usize
             ok (some (2#u8, i))
        else ok none
      else ok none

/-- [aspis_r1_cost_probe::compact::compact_row]:
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 80:0-82:1 -/
def compact.compact_row (row : Std.U8) : Result Bool := do
  ok (row >= 14#u8)

/-- [aspis_r1_cost_probe::compact::SEMANTIC_ROWS]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 29:0-29:33
    Visibility: public -/
@[global_simps, irreducible] def compact.SEMANTIC_ROWS : Std.U8 := 27#u8

/-- [aspis_r1_cost_probe::input::expand_semantic]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 154:4-172:1
    Visibility: public -/
@[rust_loop_body]
def compact.expand_semantic_loop.body
  (ext : Slice Std.U8 → Slice Std.U8 → Result ((core.result.Result Unit AspisR1CurrentCaller.compact.CodecError) × Slice Std.U8))
  (input : Slice Std.U8) (iter : core.ops.range.Range Std.U8)
  (out : Slice Std.U8) (src : Std.Usize) (dst : Std.Usize) :
  Result (ControlFlow ((core.ops.range.Range Std.U8) × (Slice Std.U8) ×
    Std.Usize × Std.Usize) ((core.result.Result Unit AspisR1CurrentCaller.compact.CodecError) ×
    (Slice Std.U8)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU8 iter
  match o with
  | none =>
    let i := Slice.len input
    if src != i
    then ok (done (core.result.Result.Err AspisR1CurrentCaller.compact.CodecError.Length, out))
    else
      let i1 := Slice.len out
      if dst != i1
      then ok (done (core.result.Result.Err AspisR1CurrentCaller.compact.CodecError.Length, out))
      else ok (done (core.result.Result.Ok (), out))
  | some row =>
    let o1 ← r1_wire.row_shape row
    let r ← core.option.Option.ok_or o1 AspisR1CurrentCaller.compact.CodecError.Length
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (_, size) := val
      let i ← dst + 5#usize
      let (s, index_mut_back) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) out
          { start := dst, «end» := i }
      let i1 ← src + 5#usize
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) input
          { start := src, «end» := i1 }
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
      let out1 := index_mut_back s2
      let b ← compact.compact_row row
      if b
      then
        let i2 ← size / 2#usize
        let i3 ← i1 + i2
        let s3 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) input
            { start := i1, «end» := i3 }
        let i4 ← i + size
        let (s4, index_mut_back1) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) out1
            { start := i, «end» := i4 }
        let (r1, s5) ← ext s3 s4
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let out2 := index_mut_back1 s5
          let src1 ← i1 + i2
          ok (cont (iter1, out2, src1, i4))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame AspisR1CurrentCaller.compact.CodecError) residual
          let out2 := index_mut_back1 s5
          ok (done (r2, out2))
      else
        let i2 ← i + size
        let (s3, index_mut_back1) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) out1
            { start := i, «end» := i2 }
        let i3 ← i1 + size
        let s4 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) input
            { start := i1, «end» := i3 }
        let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
        let out2 := index_mut_back1 s5
        ok (cont (iter1, out2, i3, i2))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame AspisR1CurrentCaller.compact.CodecError) residual
      ok (done (r1, out))

/-- [aspis_r1_cost_probe::input::expand_semantic]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 154:4-172:1
    Visibility: public -/
@[rust_loop]
def compact.expand_semantic_loop
  (ext : Slice Std.U8 → Slice Std.U8 → Result ((core.result.Result Unit AspisR1CurrentCaller.compact.CodecError) × Slice Std.U8))
  (iter : core.ops.range.Range Std.U8) (input : Slice Std.U8)
  (out : Slice Std.U8) (src : Std.Usize) (dst : Std.Usize) :
  Result ((core.result.Result Unit AspisR1CurrentCaller.compact.CodecError) × (Slice Std.U8))
  := do
  loop
    (fun (iter1, out1, src1, dst1) => compact.expand_semantic_loop.body ext input
      iter1 out1 src1 dst1)
    (iter, out, src, dst)

/-- [aspis_r1_cost_probe::input::expand_semantic]:
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 148:0-172:1
    Visibility: public -/
def compact.expand_semantic
  (ext : Slice Std.U8 → Slice Std.U8 → Result ((core.result.Result Unit AspisR1CurrentCaller.compact.CodecError) × Slice Std.U8))
  (input : Slice Std.U8) (out : Slice Std.U8) :
  Result ((core.result.Result Unit AspisR1CurrentCaller.compact.CodecError) × (Slice Std.U8))
  := do
  let i := Slice.len input
  let i1 ← compact.COMPACT_SEMANTIC
  if i != i1
  then ok (core.result.Result.Err AspisR1CurrentCaller.compact.CodecError.Length, out)
  else
    let i2 := Slice.len out
    let i3 ← compact.LOGICAL_SEMANTIC
    if i2 != i3
    then ok (core.result.Result.Err AspisR1CurrentCaller.compact.CodecError.Length, out)
    else
      let (s, index_mut_back) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) out
          { «end» := 32#usize }
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) input
          { «end» := 32#usize }
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
      let out1 := index_mut_back s2
      compact.expand_semantic_loop ext
        { start := 0#u8, «end» := compact.SEMANTIC_ROWS } input out1
        32#usize 32#usize

end PRVF

open AspisS1NativeCompact

set_option maxHeartbeats 200000
theorem PRVEq.S1NC.SEMANTIC_COMPACT_VALUES_i1 : @PRVF.compact.SEMANTIC_COMPACT_VALUES = @AspisS1NativeCompact.compact.SEMANTIC_COMPACT_VALUES := by
  delta PRVF.compact.SEMANTIC_COMPACT_VALUES AspisS1NativeCompact.compact.SEMANTIC_COMPACT_VALUES; rfl
theorem PRVEq.S1NC.SEMANTIC_BYTES_i1 : @PRVF.verifier.SEMANTIC_BYTES = @AspisS1NativeCompact.verifier.SEMANTIC_BYTES := by
  delta PRVF.verifier.SEMANTIC_BYTES AspisS1NativeCompact.verifier.SEMANTIC_BYTES; rfl
theorem PRVEq.S1NC.LOGICAL_SEMANTIC_i1 : @PRVF.compact.LOGICAL_SEMANTIC = @AspisS1NativeCompact.compact.LOGICAL_SEMANTIC := by
  delta PRVF.compact.LOGICAL_SEMANTIC AspisS1NativeCompact.compact.LOGICAL_SEMANTIC
  rw [PRVEq.S1NC.SEMANTIC_BYTES_i1]
theorem PRVEq.S1NC.COMPACT_SEMANTIC_i1 : @PRVF.compact.COMPACT_SEMANTIC = @AspisS1NativeCompact.compact.COMPACT_SEMANTIC := by
  delta PRVF.compact.COMPACT_SEMANTIC AspisS1NativeCompact.compact.COMPACT_SEMANTIC
  rw [PRVEq.S1NC.SEMANTIC_COMPACT_VALUES_i1, PRVEq.S1NC.LOGICAL_SEMANTIC_i1]
/-- Encoding difference: the emission constant is a plain Usize, the gate constant is Result-wrapped. -/
theorem PRVEq.S1NC.POINTS_i1 : (ok PRVF.r1_wire.POINTS : Result Std.Usize) = AspisS1NativeCompact.r1_wire.POINTS := by
  delta PRVF.r1_wire.POINTS AspisS1NativeCompact.r1_wire.POINTS; rfl
theorem PRVEq.S1NC.LANES_i1 : @PRVF.r1_wire.LANES = @AspisS1NativeCompact.r1_wire.LANES := by
  delta PRVF.r1_wire.LANES AspisS1NativeCompact.r1_wire.LANES; rfl
theorem PRVEq.S1NC.CLAIMS_i1 : @PRVF.r1_wire.CLAIMS = @AspisS1NativeCompact.r1_wire.CLAIMS := by
  delta PRVF.r1_wire.CLAIMS AspisS1NativeCompact.r1_wire.CLAIMS
  rw [← PRVEq.S1NC.POINTS_i1, PRVEq.S1NC.LANES_i1]; rfl
theorem PRVEq.S1NC.row_shape_i1 : @PRVF.r1_wire.row_shape = @AspisS1NativeCompact.r1_wire.row_shape := by
  funext row
  delta PRVF.r1_wire.row_shape AspisS1NativeCompact.r1_wire.row_shape
  rw [PRVEq.S1NC.CLAIMS_i1, PRVEq.S1NC.LANES_i1]
  all_goals rfl
theorem PRVEq.S1NC.compact_row_i1 : @PRVF.compact.compact_row = @AspisS1NativeCompact.compact.compact_row := rfl
theorem PRVEq.S1NC.SEMANTIC_ROWS_i1 : @PRVF.compact.SEMANTIC_ROWS = @AspisS1NativeCompact.compact.SEMANTIC_ROWS := by
  delta PRVF.compact.SEMANTIC_ROWS AspisS1NativeCompact.compact.SEMANTIC_ROWS; rfl

theorem PRVEq.S1NC.expand_semantic_loop.body_i1 (ops : AspisS1NativeCompact.Ops) :
    @PRVF.compact.expand_semantic_loop.body ops.expandValues = @AspisS1NativeCompact.compact.expand_semantic_loop.body ops := by
  funext input iter out src dst
  delta PRVF.compact.expand_semantic_loop.body AspisS1NativeCompact.compact.expand_semantic_loop.body
  simp only [PRVEq.S1NC.row_shape_i1, PRVEq.S1NC.compact_row_i1]
  all_goals rfl

theorem PRVEq.S1NC.expand_semantic_loop_i1 (ops : AspisS1NativeCompact.Ops) :
    @PRVF.compact.expand_semantic_loop ops.expandValues = @AspisS1NativeCompact.compact.expand_semantic_loop ops := by
  funext iter input out src dst
  delta PRVF.compact.expand_semantic_loop AspisS1NativeCompact.compact.expand_semantic_loop
  simp only [PRVEq.S1NC.expand_semantic_loop.body_i1]
  all_goals rfl

theorem PRVEq.S1NC.expand_semantic_i1 (ops : AspisS1NativeCompact.Ops) :
    @PRVF.compact.expand_semantic ops.expandValues = @AspisS1NativeCompact.compact.expand_semantic ops := by
  funext input out
  delta PRVF.compact.expand_semantic AspisS1NativeCompact.compact.expand_semantic
  simp only [PRVEq.S1NC.COMPACT_SEMANTIC_i1, PRVEq.S1NC.LOGICAL_SEMANTIC_i1, PRVEq.S1NC.SEMANTIC_ROWS_i1, PRVEq.S1NC.expand_semantic_loop_i1]
  all_goals rfl

#print axioms PRVEq.S1NC.SEMANTIC_COMPACT_VALUES_i1
#print axioms PRVEq.S1NC.SEMANTIC_BYTES_i1
#print axioms PRVEq.S1NC.LOGICAL_SEMANTIC_i1
#print axioms PRVEq.S1NC.COMPACT_SEMANTIC_i1
#print axioms PRVEq.S1NC.POINTS_i1
#print axioms PRVEq.S1NC.LANES_i1
#print axioms PRVEq.S1NC.CLAIMS_i1
#print axioms PRVEq.S1NC.row_shape_i1
#print axioms PRVEq.S1NC.compact_row_i1
#print axioms PRVEq.S1NC.SEMANTIC_ROWS_i1
#print axioms PRVEq.S1NC.expand_semantic_loop.body_i1
#print axioms PRVEq.S1NC.expand_semantic_loop_i1
#print axioms PRVEq.S1NC.expand_semantic_i1
