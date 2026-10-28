import R1Z.ProverRwQueryInstalled
/-! Exact emitted caller with its proved query component installed. Generated
by tools/prover-rw-20261023/query-composition.py; no native source change. -/
set_option autoImplicit false
namespace R1Z.ProverRwQueryOpening
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

def opening
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (prepared : prover.PreparedOpening)
  (folded_salts : host_commitment.PrivateSalts) :
  Result (core.result.Result prover.Publication verifier.Error)
  := do
  let s := alloc.vec.Vec.deref prepared.folded_word
  let leaves ← prover.folded_leaves hash s folded_salts
  let o ←
    host_tree.BinaryTree.new
      aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 hash leaves
  let r ← core.option.Option.ok_or o verifier.Error.Allocation
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let root ← host_tree.BinaryTree.root val
    let s1 := alloc.vec.Vec.deref prepared.q1
    let s2 := alloc.vec.Vec.deref prepared.w1
    let c1 ← prover.round s1 s2
    let s3 ← Aeneas.Std.lift (Array.to_slice c1)
    let c1bytes ← prover.encoded_slice s3
    let s4 ← Aeneas.Std.lift (Array.to_slice root)
    let payload ← alloc.slice.Slice.to_vec core.clone.CloneU8 s4
    let s5 := alloc.vec.Vec.deref c1bytes
    let payload1 ←
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 payload s5
    let s6 := alloc.vec.Vec.deref payload1
    let (alpha1, transcript) ←
      host_transcript.Transcript.scalar
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        prepared.transcript 30#u8 s6 false
    let s7 := alloc.vec.Vec.deref prepared.q1
    let final_message ← prover.fold s7 alpha1 false
    let s8 := alloc.vec.Vec.deref final_message
    let fbytes ← prover.encoded_slice s8
    let s9 := alloc.vec.Vec.deref fbytes
    let (r1, transcript1) ←
      ProverRwQueryInstalled.query
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        transcript 31#u8 s9
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let s10 ← Aeneas.Std.lift (Array.to_slice (Std.Array.empty Std.U8))
      let _ ←
        host_transcript.Transcript.scalar_k
          aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
          transcript1 32#u8 s10
      let scp ← Array.index_usize prepared.sem.z 0#usize
      let scp1 ← Array.index_usize prepared.sem.z 1#usize
      let s11 ← Aeneas.Std.lift (Array.to_slice val1)
      let v ← alloc.slice.Slice.to_vec core.clone.CloneU32 s11
      let a ← Array.index_usize prepared.sem.roots 0#usize
      let r2 ←
        prover.public_check variant
          {
            alpha := prepared.sem.alpha,
            z :=
              (Array.make 2#usize [
                Array.make 2#usize [ scp.x, scp.y ],
                Array.make 2#usize [ scp1.x, scp1.y ]
                ]),
            gamma := prepared.gamma,
            kappa := prepared.kappa,
            alpha0 := prepared.alpha0,
            alpha1,
            queries := v
          } a
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        ok (core.result.Result.Ok
          {
            backend := prepared.backend,
            semantic_bytes := prepared.sem.bytes,
            y1 := prepared.y1,
            inactive := prepared.inactive,
            c0bytes := prepared.c0bytes,
            root,
            c1bytes,
            fbytes,
            queries := val1,
            folded_word := prepared.folded_word,
            folded_salts,
            tree := val
          })
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          prover.Publication (core.convert.FromSame verifier.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        prover.Publication (core.convert.FromSame verifier.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      prover.Publication (core.convert.FromSame verifier.Error) residual

set_option backward.isDefEq.respectTransparency false in
theorem opening_exact (variant : transport.Variant)
    (h : Slice (Slice U8) → Result (Array U8 32#usize))
    (prepared : prover.PreparedOpening) (salts : host_commitment.PrivateSalts) :
    prover.finish_opening variant h prepared salts = opening variant h prepared salts := by
  simp only [prover.finish_opening,opening,ProverRwQueryInstalled.query_exact]
  try rfl

#print axioms opening_exact
end R1Z.ProverRwQueryOpening
