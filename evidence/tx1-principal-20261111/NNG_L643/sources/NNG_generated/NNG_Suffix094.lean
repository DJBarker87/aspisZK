import NNG_Context094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Suffix094
open Aeneas Aeneas.Std Result NMT_tx1 NNG_Context094

def f_markCheckpointWrite {H : Type} (c : Calls) (parent : Parent H) (bytes : alloc.vec.Vec U8) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  c.c11 obs verifier.Phase.CheckpointWrite
  ok (core.result.Result.Ok bytes)

def f_bytes {H : Type} (c : Calls) (parent : Parent H) (val : verifier.Prepared) (a : verifier.Accumulator) (v : alloc.vec.Vec aspis_core.field.QM31) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let bytes ←
    c.c6 aspis_coredigestDigest32Inst val
      { a with weights := v } proof public_bytes hash
  f_markCheckpointWrite c parent bytes

def f_s3 {H : Type} (c : Calls) (parent : Parent H) (val : verifier.Prepared) (a : verifier.Accumulator) (pending : verifier.BatchedWeights) (s2 : Slice aspis_core.field.QM31) (deref_mut_back : Slice aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let s3 ← c.c7 pending s2
  let v := deref_mut_back s3
  f_bytes c parent val a v

def f_s2 {H : Type} (c : Calls) (parent : Parent H) (val : verifier.Prepared) (a : verifier.Accumulator) (pending : verifier.BatchedWeights) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let (s2, deref_mut_back) ←
    lift (alloc.vec.Vec.deref_mut a.weights)
  f_s3 c parent val a pending s2 deref_mut_back

def f_r8 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (val2 : verifier.QueryGeometry) (val3 : verifier.BatchedWeights) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let r8 ←
    c.c4 proof val val1 g1 obs val2
      val3 k
  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r8
  match cf7 with
  | core.ops.control_flow.ControlFlow.Continue val4 =>
    let (a, pending) := val4
    f_s2 c parent val a pending
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame
      verifier.Error) residual

def f_r7 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (val2 : verifier.QueryGeometry) (s1 : Slice aspis_core.field.QM31) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let r7 ← c.c8 s1
  let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
  match cf6 with
  | core.ops.control_flow.ControlFlow.Continue val3 =>
    f_r8 c parent g1 val val1 val2 val3
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame
      verifier.Error) residual

def f_r6 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let r6 ← c.c9 val.queries 0#usize k
  let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
  match cf5 with
  | core.ops.control_flow.ControlFlow.Continue val2 =>
    let s1 := alloc.vec.Vec.deref val1.weights
    f_r7 c parent g1 val val1 val2 s1
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
      residual

def f_markMerkle {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  c.c11 obs (verifier.Phase.Merkle 0#usize)
  f_r6 c parent g1 val val1

def f_r5 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (folded_root : Array U8 32#usize) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let r5 ←
    c.c3 aspis_coredigestDigest32Inst
      proof val folded_root 0#usize hash
  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
  match cf4 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    f_markMerkle c parent g1 val val1
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
      residual

def f_folded_root {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (r4 : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let folded_root ←
    core.result.Result.unwrap core.fmt.DebugTryFromSliceError r4
  f_r5 c parent g1 val val1 folded_root

def f_r4 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (s : Slice U8) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let r4 ←
    core.array.TryFromArrayCopySlice.try_from 32#usize
      core.marker.CopyU8 s
  f_folded_root c parent g1 val val1 r4

def f_s {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (i : Usize) (i1 : Usize) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let s ←
    core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
      { start := i, «end» := i1 }
  f_r4 c parent g1 val val1 s

def f_i1 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (i : Usize) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let i1 ← compact.OFF_ROUND1
  f_s c parent g1 val val1 i i1

def f_i {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let i ← compact.OFF_FOLDED_ROOT
  f_i1 c parent g1 val val1 i

def f_markPrepare {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  c.c11 obs verifier.Phase.Prepare
  f_i c parent g1 val val1

def f_r3 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let r3 ← c.c10 transport.Variant.S2
  let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf3 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    f_markPrepare c parent g1 val val1
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
      residual

def f_r2 {H : Type} (c : Calls) (parent : Parent H) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let (r2, g1) ←
    c.c5 aspis_coredigestDigest32Inst public1 proof
      hash obs g
  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
  match cf2 with
  | core.ops.control_flow.ControlFlow.Continue val =>
    f_r3 c parent g1 val
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
      residual

def f_we {H : Type} (c : Calls) (parent : Parent H) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let we ← c.c0
  let g := Array.repeat 29#usize we
  f_r2 c parent g

def f_markParsed {H : Type} (c : Calls) (parent : Parent H) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  c.c11 obs verifier.Phase.Parsed
  f_we c parent

def f_r1 {H : Type} (c : Calls) (parent : Parent H) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let r1 ← c.c2 proof
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    f_markParsed c parent
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
      residual

def f_r {H : Type} (c : Calls) (parent : Parent H) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let r ← c.c1 proof
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    f_r1 c parent
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual

def f_guard {H : Type} (c : Calls) (parent : Parent H) : Result Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  if k != compact.SPLIT
  then ok (core.result.Result.Err verifier.Error.Parse)
  else
    f_r c parent

theorem source {H : Type} (c : Calls) (parent : Parent H) :
 f_guard c parent=NNG_Context094.body c parent := by rfl
#print axioms source
end AspisR1.NNG_Suffix094
