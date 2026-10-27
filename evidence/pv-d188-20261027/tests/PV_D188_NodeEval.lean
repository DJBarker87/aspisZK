import Aeneas
import R1Z.ProverRwFullTypes
import R1Z.ProverRwP7CurrentFieldSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
namespace PV_D188_NodeEval
abbrev aspis_core.field.M31 := ProverRwFull.aspis_core.field.M31
abbrev aspis_core.field.CM31 := ProverRwFull.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := ProverRwFull.aspis_core.field.QM31
abbrev aspis_prover.state_only_hiding.StateOnlyMaskBuildError := ProverRwFull.aspis_prover.state_only_hiding.StateOnlyMaskBuildError
abbrev aspis_core.field.M31.add := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.add
abbrev aspis_core.field.M31.sub := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.sub
abbrev aspis_core.field.M31.mul := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.mul
abbrev aspis_core.field.M31.double := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.double
abbrev aspis_core.field.QM31.add := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add
abbrev aspis_core.field.QM31.mul := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul
abbrev aspis_core.field.QM31.mul_m31 := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31
abbrev aspis_core.field.CM31.sub := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.sub
def aspis_core.field.M31.ZERO : Result U32 := ok 0#u32
def aspis_core.field.M31.ONE : Result U32 := ok 1#u32
def aspis_core.field.QM31.ZERO : Result aspis_core.field.QM31 := ok R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ZERO
def aspis_core.field.QM31.ONE : Result aspis_core.field.QM31 := ok R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ONE
def aspis_core.field.QM31.sub (a b : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
 let c0 ← aspis_core.field.CM31.sub a.c0 b.c0
 let c1 ← aspis_core.field.CM31.sub a.c1 b.c1
 ok {c0,c1}
def aspis_statement.state_only_poseidon.STATE_ONLY_POSEIDON_TRACE_ROWS : Result Usize := ok 1024#usize
def multiproof.LEAF_BITS : Result U32 := ok 18#u32
def multiproof.MAX_BATCH : Result Usize := ok 16#usize

def host_tree.count_parent
  (level : Array Std.U32 16#usize) (i : Std.Usize) (n : Std.Usize) :
  Result (Std.U32 × Std.Usize)
  := do
  let i1 ← Array.index_usize level i
  let parent ← Aeneas.Std.lift (Std.U32.wrapping_shr i1 1#u32)
  let i2 ← Aeneas.Std.lift (Std.Usize.wrapping_add i 1#usize)
  if i2 < n
  then
    let i3 ← Aeneas.Std.lift (Std.Usize.wrapping_add i 1#usize)
    let i4 ← Array.index_usize level i3
    let i5 ← Aeneas.Std.lift (Std.U32.wrapping_shr i4 1#u32)
    if i5 = parent
    then ok (parent, 2#usize)
    else ok (parent, 1#usize)
  else ok (parent, 1#usize)

def host_tree.count_level_loop.body
  (n : Std.Usize) (level : Array Std.U32 16#usize) (i : Std.Usize)
  (w : Std.Usize) (missing : Std.Usize) :
  Result (ControlFlow ((Array Std.U32 16#usize) × Std.Usize × Std.Usize ×
    Std.Usize) ((Array Std.U32 16#usize) × Std.Usize × Std.Usize))
  := do
  if i < n
  then
    let (parent, take) ← host_tree.count_parent level i n
    let level1 ← Array.update level w parent
    let w1 ← Aeneas.Std.lift (Std.Usize.wrapping_add w 1#usize)
    let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_add i take)
    let i2 ← Aeneas.Std.lift (Std.Usize.wrapping_sub 2#usize take)
    let missing1 ← Aeneas.Std.lift (Std.Usize.wrapping_add missing i2)
    ok (cont (level1, i1, w1, missing1))
  else ok (done (level, w, missing))

def host_tree.count_level_loop
  (level : Array Std.U32 16#usize) (n : Std.Usize) (i : Std.Usize)
  (w : Std.Usize) (missing : Std.Usize) :
  Result ((Array Std.U32 16#usize) × Std.Usize × Std.Usize)
  := do
  loop
    (fun (level1, i1, w1, missing1) => host_tree.count_level_loop.body n level1
      i1 w1 missing1)
    (level, i, w, missing)

def host_tree.count_level
  (level : Array Std.U32 16#usize) (n : Std.Usize) :
  Result ((Array Std.U32 16#usize) × Std.Usize × Std.Usize)
  := do
  host_tree.count_level_loop level n 0#usize 0#usize 0#usize

def host_tree.count_levels
  (level : Array Std.U32 16#usize) (n : Std.Usize) (depth : Std.U32)
  (count : Std.Usize) (bits : Std.U32) :
  Result Std.Usize
  := do
  if depth = bits
  then ok count
  else
    let (level1, n1, missing) ← host_tree.count_level level n
    let i ← Aeneas.Std.lift (Std.U32.wrapping_add depth 1#u32)
    let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_add count missing)
    host_tree.count_levels level1 n1 i i1 bits
partial_fixpoint

def host_tree.check_indices_loop.body
  (indices : Slice Std.U32) (i : Std.Usize) :
  Result (ControlFlow Std.Usize (Option (Option Unit)))
  := do
  let i1 := Slice.len indices
  if i < i1
  then
    let i2 ← Slice.index_usize indices i
    let i3 ← multiproof.LEAF_BITS
    let i4 ← Aeneas.Std.lift (Std.U32.wrapping_shl 1#u32 (UScalar.cast .U32 i3))
    if i2 >= i4
    then ok (done none)
    else
      if i > 0#usize
      then
        let i5 ← Aeneas.Std.lift (Std.Usize.wrapping_sub i 1#usize)
        let i6 ← Slice.index_usize indices i5
        if i6 >= i2
        then ok (done none)
        else let i7 ← Aeneas.Std.lift (Std.Usize.wrapping_add i 1#usize)
             ok (cont i7)
      else let i5 ← Aeneas.Std.lift (Std.Usize.wrapping_add i 1#usize)
           ok (cont i5)
  else ok (done (some (some ())))

def host_tree.check_indices_loop
  (indices : Slice Std.U32) (i : Std.Usize) :
  Result (Option (Option Unit))
  := do
  loop
    (fun i1 => host_tree.check_indices_loop.body indices i1)
    i

def host_tree.check_indices
  (indices : Slice Std.U32) : Result (Option Unit) := do
  let b ← core.slice.Slice.is_empty indices
  if b
  then ok none
  else
    let i := Slice.len indices
    let i1 ← multiproof.MAX_BATCH
    if i > i1
    then ok none
    else
      let pending_return ← host_tree.check_indices_loop indices 0#usize
      match pending_return with
      | none => ok none
      | some o => ok o

def host_tree.node_count
  (indices : Slice Std.U32) : Result (Option Std.Usize) := do
  let o ← host_tree.check_indices indices
  let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let level := Array.repeat 16#usize 0#u32
    let i := Slice.len indices
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) level
        { «end» := i }
    let s1 ← core.slice.Slice.copy_from_slice core.marker.CopyU32 s indices
    let level1 := index_mut_back s1
    let i1 := Slice.len indices
    let i2 ← multiproof.LEAF_BITS
    let i3 ← host_tree.count_levels level1 i1 0#u32 0#usize i2
    ok (some i3)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      Std.Usize residual
#eval (do let s ← lift (Array.to_slice (Array.make 3#usize [1#u32,2#u32,3#u32]))
          let n ← host_tree.node_count s
          ok (n.map (fun x => x.val)) : Result (Option Nat))
end PV_D188_NodeEval
