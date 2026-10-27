import R1Z.PDict_FmtQueryOpenings
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
def publicationFrame (ops : ExternalFuns)
  (semantic : Slice U8 → alloc.vec.Vec U8 → Result ((core.result.Result Unit compact.CodecError) × alloc.vec.Vec U8))
  (query : alloc.vec.Vec U8 → host_commitment.Commitment → host_commitment.Commitment → Array U32 22#usize → Slice aspis_core.field.wide_exact.WideExact → host_commitment.PrivateSalts → Result (alloc.vec.Vec U8))
  (nodes : alloc.vec.Vec U8 → host_commitment.Commitment → host_commitment.Commitment → host_tree.BinaryTree → Array U32 22#usize → Result (core.result.Result (alloc.vec.Vec U8) verifier.Error))
  (variant : transport.Variant) (p : prover.Publication) :
  Result (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error)
  :=
  letI : ExternalFuns := ops
  do
  let i ← compact.PROOF_BYTES
  let out := alloc.vec.Vec.with_capacity Std.U8 i
  let a ← compact.MAGIC
  let s ← Aeneas.Std.lift (Array.to_slice a)
  let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s
  let i1 ← transport.Variant.tag variant
  let s1 ←
    Aeneas.Std.lift (Array.to_slice
      (Array.make 8#usize [ i1, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8 ]))
  let out2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out1 s1
  let s2 := alloc.vec.Vec.deref p.semantic_bytes
  let (r, out3) ← semantic s2 out2
  let r1 ←
    core.result.Result.map_err
      prover.publish_compact.closure.Insts.CoreOpsFunctionFnOnceTupleCodecErrorError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let s3 := alloc.vec.Vec.deref p.y1
    let (r2, out4) ← host_compact.compact_values s3 out3
    let r3 ←
      core.result.Result.map_err
        prover.publish_compact.closure_1.Insts.CoreOpsFunctionFnOnceTupleCodecErrorError
        r2 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let a1 ← aspis_core.field.wide_exact.WideExact.to_le_bytes p.inactive
      let s4 ← Aeneas.Std.lift (Array.to_slice a1)
      let out5 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out4 s4
      let s5 := alloc.vec.Vec.deref p.c0bytes
      let out6 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out5 s5
      let s6 ← Aeneas.Std.lift (Array.to_slice p.root)
      let out7 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out6 s6
      let s7 := alloc.vec.Vec.deref p.c1bytes
      let out8 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out7 s7
      let s8 := alloc.vec.Vec.deref p.fbytes
      let out9 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out8 s8
      let left_val := alloc.vec.Vec.len out9
      let right_val ← compact.OFF_OPENINGS
      massert (left_val = right_val)
      let (o, _) := core.option.Option.take p.backend.c1
      let cc1 ← core.option.Option.unwrap o
      let (o1, _) := core.option.Option.take p.backend.c2
      let cc2 ← core.option.Option.unwrap o1
      let s9 := alloc.vec.Vec.deref p.folded_word
      let out10 ←
        query out9 cc1 cc2 p.queries s9 p.folded_salts
      let left_val1 := alloc.vec.Vec.len out10
      let right_val1 ← compact.OFF_NODES
      massert (left_val1 = right_val1)
      let r4 ← nodes out10 cc1 cc2 p.tree p.queries
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let left_val2 := alloc.vec.Vec.len val
        massert (left_val2 = i)
        ok (core.result.Result.Ok val)
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual

theorem publication_frame (ops : ExternalFuns) :
    @prover.publish_compact _ ops = publicationFrame ops
      (@host_compact.compact_semantic _ ops)
      (@prover.append_query_openings _ ops) (@prover.append_node_slots _ ops) := rfl
#print axioms publication_frame

theorem erase_420 (ops other : ExternalFuns) :
    @prover.publish_compact _ (replace ops other) = @prover.publish_compact _ ops := by
  rw [publication_frame, publication_frame, erase_396 ops other,
    erase_419 ops other, erase_405 ops other]
  unfold publicationFrame
  rfl
#print axioms erase_420
end R1Z.PDict_FmtErase
