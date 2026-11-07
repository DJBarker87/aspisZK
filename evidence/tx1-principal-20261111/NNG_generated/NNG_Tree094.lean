import NNG_Suffix094
import NMT_CallTree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Tree094
open Aeneas Aeneas.Std Result NMT_tx1 NNG_Context094 NMT_CallTree
def NNG_call_0 (NMT_call_0 : Result aspis_core.field.wide_exact.WideExact)  : Code aspis_core.field.wide_exact.WideExact :=
 invoke "aspis_core.field.wide_exact.WideExact.ZERO" () (NMT_call_0)
def NNG_call_1 (NMT_call_1 : (Slice Std.U8) → Result (core.result.Result transport.Variant
    verifier.Error))  (a0 : (Slice Std.U8)) : Code (core.result.Result transport.Variant verifier.Error) :=
 invoke "verifier.candidate.parse_shape" a0 (NMT_call_1 a0)
def NNG_call_2 (NMT_call_2 : (Slice Std.U8) → Result (core.result.Result Unit verifier.Error))  (a0 : (Slice Std.U8)) : Code (core.result.Result Unit verifier.Error) :=
 invoke "verifier.candidate.canonical_scan" a0 (NMT_call_2 a0)
def NNG_call_3 (NMT_call_3 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H), (Slice Std.U8) → verifier.Prepared → (Array Std.U8 32#usize) →
    Std.Usize → H → Result (core.result.Result Unit verifier.Error)) {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (a0 : (Slice Std.U8)) (a1 : verifier.Prepared) (a2 : (Array Std.U8 32#usize)) (a3 : Std.Usize) (a4 : H) : Code (core.result.Result Unit verifier.Error) :=
 invoke "verifier.candidate.batch_merkle" (aspis_coredigestDigest32Inst,a0,a1,a2,a3,a4) (NMT_call_3 aspis_coredigestDigest32Inst a0 a1 a2 a3 a4)
def NNG_call_4 (NMT_call_4 : (Slice Std.U8) → verifier.Prepared → verifier.Accumulator → (Array
    aspis_core.field.wide_exact.WideExact 29#usize) → (Option (verifier.Phase
    → Result Unit)) → verifier.QueryGeometry → verifier.BatchedWeights
    → Std.Usize → Result (core.result.Result (verifier.Accumulator ×
    verifier.BatchedWeights) verifier.Error))  (a0 : (Slice Std.U8)) (a1 : verifier.Prepared) (a2 : verifier.Accumulator) (a3 : (Array aspis_core.field.wide_exact.WideExact 29#usize)) (a4 : (Option (verifier.Phase → Result Unit))) (a5 : verifier.QueryGeometry) (a6 : verifier.BatchedWeights) (a7 : Std.Usize) : Code (core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error) :=
 invoke "verifier.candidate.query_loop" (a0,a1,a2,a3,a4,a5,a6,a7) (NMT_call_4 a0 a1 a2 a3 a4 a5 a6 a7)
def NNG_call_5 (NMT_call_5 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H), aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → (Slice
    Std.U8) → H → (Option (verifier.Phase → Result Unit)) → (Array
    aspis_core.field.wide_exact.WideExact 29#usize) → Result
    ((core.result.Result verifier.Prepared verifier.Error) × (Array
    aspis_core.field.wide_exact.WideExact 29#usize))) {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (a0 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (a1 : (Slice Std.U8)) (a2 : H) (a3 : (Option (verifier.Phase → Result Unit))) (a4 : (Array aspis_core.field.wide_exact.WideExact 29#usize)) : Code ((core.result.Result verifier.Prepared verifier.Error) × (Array aspis_core.field.wide_exact.WideExact 29#usize)) :=
 invoke "TX1:087/prepare" (a0,a1,a2,a3,a4) (NMT_call_5 aspis_coredigestDigest32Inst a0 a1 a2 a3 a4)
def NNG_call_6 (NMT_call_6 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H), verifier.Prepared → verifier.Accumulator → (Slice Std.U8) → (Slice
    Std.U8) → H → Result (alloc.vec.Vec Std.U8)) {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (a0 : verifier.Prepared) (a1 : verifier.Accumulator) (a2 : (Slice Std.U8)) (a3 : (Slice Std.U8)) (a4 : H) : Code (alloc.vec.Vec Std.U8) :=
 invoke "verifier.checkpoint" (aspis_coredigestDigest32Inst,a0,a1,a2,a3,a4) (NMT_call_6 aspis_coredigestDigest32Inst a0 a1 a2 a3 a4)
def NNG_call_7 (NMT_call_7 : verifier.BatchedWeights → (Slice aspis_core.field.QM31) → Result (Slice
    aspis_core.field.QM31))  (a0 : verifier.BatchedWeights) (a1 : (Slice aspis_core.field.QM31)) : Code (Slice aspis_core.field.QM31) :=
 invoke "verifier.BatchedWeights.finish" (a0,a1) (NMT_call_7 a0 a1)
def NNG_call_8 (NMT_call_8 : (Slice aspis_core.field.QM31) → Result (core.result.Result
    verifier.BatchedWeights verifier.Error))  (a0 : (Slice aspis_core.field.QM31)) : Code (core.result.Result verifier.BatchedWeights verifier.Error) :=
 invoke "verifier.BatchedWeights.new" a0 (NMT_call_8 a0)
def NNG_call_9 (NMT_call_9 : (Array Std.U32 22#usize) → Std.Usize → Std.Usize → Result
    (core.result.Result verifier.QueryGeometry verifier.Error))  (a0 : (Array Std.U32 22#usize)) (a1 : Std.Usize) (a2 : Std.Usize) : Code (core.result.Result verifier.QueryGeometry verifier.Error) :=
 invoke "verifier.QueryGeometry.for_range" (a0,a1,a2) (NMT_call_9 a0 a1 a2)
def NNG_call_10 (NMT_call_10 : transport.Variant → Result (core.result.Result verifier.Accumulator
    verifier.Error))  (a0 : transport.Variant) : Code (core.result.Result verifier.Accumulator verifier.Error) :=
 invoke "verifier.Accumulator.new" a0 (NMT_call_10 a0)
def NNG_call_11 (NMT_call_11 : (Option (verifier.Phase → Result Unit)) → verifier.Phase → Result Unit)  (a0 : (Option (verifier.Phase → Result Unit))) (a1 : verifier.Phase) : Code Unit :=
 invoke "verifier.mark" (a0,a1) (NMT_call_11 a0 a1)


def f_markCheckpointWrite {H : Type} (c : Calls) (parent : Parent H) (bytes : alloc.vec.Vec U8) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  (NNG_call_11 c.c11) obs verifier.Phase.CheckpointWrite
  pure (core.result.Result.Ok bytes)

def f_bytes {H : Type} (c : Calls) (parent : Parent H) (val : verifier.Prepared) (a : verifier.Accumulator) (v : alloc.vec.Vec aspis_core.field.QM31) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let bytes ←
    (NNG_call_6 c.c6) aspis_coredigestDigest32Inst val
      { a with weights := v } proof public_bytes hash
  f_markCheckpointWrite c parent bytes

def f_s3 {H : Type} (c : Calls) (parent : Parent H) (val : verifier.Prepared) (a : verifier.Accumulator) (pending : verifier.BatchedWeights) (s2 : Slice aspis_core.field.QM31) (deref_mut_back : Slice aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let s3 ← (NNG_call_7 c.c7) pending s2
  let v := deref_mut_back s3
  f_bytes c parent val a v

def f_s2 {H : Type} (c : Calls) (parent : Parent H) (val : verifier.Prepared) (a : verifier.Accumulator) (pending : verifier.BatchedWeights) : Code Output := do
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

def f_r8 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (val2 : verifier.QueryGeometry) (val3 : verifier.BatchedWeights) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let r8 ←
    (NNG_call_4 c.c4) proof val val1 g1 obs val2
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

def f_r7 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (val2 : verifier.QueryGeometry) (s1 : Slice aspis_core.field.QM31) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let r7 ← (NNG_call_8 c.c8) s1
  let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
  match cf6 with
  | core.ops.control_flow.ControlFlow.Continue val3 =>
    f_r8 c parent g1 val val1 val2 val3
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame
      verifier.Error) residual

def f_r6 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let r6 ← (NNG_call_9 c.c9) val.queries 0#usize k
  let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
  match cf5 with
  | core.ops.control_flow.ControlFlow.Continue val2 =>
    let s1 := alloc.vec.Vec.deref val1.weights
    f_r7 c parent g1 val val1 val2 s1
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
      residual

def f_markMerkle {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  (NNG_call_11 c.c11) obs (verifier.Phase.Merkle 0#usize)
  f_r6 c parent g1 val val1

def f_r5 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (folded_root : Array U8 32#usize) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let r5 ←
    (NNG_call_3 c.c3) aspis_coredigestDigest32Inst
      proof val folded_root 0#usize hash
  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
  match cf4 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    f_markMerkle c parent g1 val val1
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
      residual

def f_folded_root {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (r4 : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError) : Code Output := do
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

def f_r4 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (s : Slice U8) : Code Output := do
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

def f_s {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (i : Usize) (i1 : Usize) : Code Output := do
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

def f_i1 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) (i : Usize) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let i1 ← compact.OFF_ROUND1
  f_s c parent g1 val val1 i i1

def f_i {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let i ← compact.OFF_FOLDED_ROOT
  f_i1 c parent g1 val val1 i

def f_markPrepare {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) (val1 : verifier.Accumulator) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  (NNG_call_11 c.c11) obs verifier.Phase.Prepare
  f_i c parent g1 val val1

def f_r3 {H : Type} (c : Calls) (parent : Parent H) (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) (val : verifier.Prepared) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let r3 ← (NNG_call_10 c.c10) transport.Variant.S2
  let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf3 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    f_markPrepare c parent g1 val val1
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
      residual

def f_r2 {H : Type} (c : Calls) (parent : Parent H) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let (r2, g1) ←
    (NNG_call_5 c.c5) aspis_coredigestDigest32Inst public1 proof
      hash obs g
  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
  match cf2 with
  | core.ops.control_flow.ControlFlow.Continue val =>
    f_r3 c parent g1 val
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
      residual

def f_we {H : Type} (c : Calls) (parent : Parent H) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let we ← (NNG_call_0 c.c0)
  let g := Array.repeat 29#usize we
  f_r2 c parent g

def f_markParsed {H : Type} (c : Calls) (parent : Parent H) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  (NNG_call_11 c.c11) obs verifier.Phase.Parsed
  f_we c parent

def f_r1 {H : Type} (c : Calls) (parent : Parent H) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let r1 ← (NNG_call_2 c.c2) proof
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    f_markParsed c parent
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
      residual

def f_r {H : Type} (c : Calls) (parent : Parent H) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let r ← (NNG_call_1 c.c1) proof
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    f_r1 c parent
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual

def f_guard {H : Type} (c : Calls) (parent : Parent H) : Code Output := do
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

end AspisR1.NNG_Tree094
