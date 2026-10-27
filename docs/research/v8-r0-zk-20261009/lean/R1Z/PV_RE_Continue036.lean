import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue036
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.publish_compact`.
Recursive calls remain the original extracted calls. -/
def continueAfter (variant : transport.Variant) (p : prover.Publication) (out : Payload (compact.PROOF_BYTES)) : Result (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error) := do
  let i := out
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
  let (r, out3) ← host_compact.compact_semantic s2 out2
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
        prover.append_query_openings out9 cc1 cc2 p.queries s9 p.folded_salts
      let left_val1 := alloc.vec.Vec.len out10
      let right_val1 ← compact.OFF_NODES
      massert (left_val1 = right_val1)
      let r4 ← prover.append_node_slots out10 cc1 cc2 p.tree p.queries
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

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (variant : transport.Variant) (p : prover.Publication) :
    prover.publish_compact (variant := variant) (p := p) =
      (compact.PROOF_BYTES >>= fun out => continueAfter (variant := variant) (p := p) out) := by
  rw [prover.publish_compact]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (variant : transport.Variant) (p : prover.Publication) (out : Payload (compact.PROOF_BYTES))
    (h : (compact.PROOF_BYTES) = .ok out) :
    prover.publish_compact (variant := variant) (p := p) = continueAfter (variant := variant) (p := p) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (variant : transport.Variant) (p : prover.Publication) (e : Error)
    (h : (compact.PROOF_BYTES) = .fail e) :
    prover.publish_compact (variant := variant) (p := p) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (variant : transport.Variant) (p : prover.Publication)
    (h : (compact.PROOF_BYTES) = .div) :
    prover.publish_compact (variant := variant) (p := p) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue036
