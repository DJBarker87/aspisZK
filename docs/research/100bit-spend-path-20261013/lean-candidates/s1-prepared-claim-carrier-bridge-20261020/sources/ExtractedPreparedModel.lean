import AspisR1PublicPreparation.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1PublicPreparation
structure PreparedModel.Boundaries where
  toBytes : aspis_core.field.WideExact → Result (Array U8 32#usize)
  fromQm : aspis_core.field.QM31 → Result aspis_core.field.WideExact
  ordinary : (Array U8 32#usize) → Result aspis_core.field.WideExact
  gamma : (Array U8 32#usize) → Result aspis_core.field.WideExact
  queries : {H : Type} → aspis_core.Digest32 H → transcript.Transcript H → U8 → Slice U8 →
    Result (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H)
  claim : {H : Type} → aspis_core.Digest32 H → r1_semantic.Verified H → Slice U8 →
    aspis_core.field.WideExact → aspis_core.field.WideExact → aspis_core.field.WideExact →
    Result (core.result.Result aspis_core.field.WideExact verifier.Error)

def PreparedModel.scalar (B : PreparedModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (self : transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  (nonzero : Bool) :
  Result (aspis_core.field.WideExact × (transcript.Transcript H))
  := do
  let (block, self1) ←
    transcript.Transcript.block aspis_coreDigest32Inst self row payload
  let out ←
    if nonzero
    then B.gamma block
    else B.ordinary block
  let i ← lift (UScalar.cast .Usize row)
  trace.value 4#u16 i out
  ok (out, self1)

def PreparedModel.scalar_k (B : PreparedModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (self : transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  Result (aspis_core.field.QM31 × (transcript.Transcript H))
  := do
  let (a, self1) ←
    transcript.Transcript.block aspis_coreDigest32Inst self row payload
  let out ← sampler.qm31_sample a
  let i ← lift (UScalar.cast .Usize row)
  let we ← B.fromQm out
  trace.value 4#u16 i we
  ok (out, self1)

def PreparedModel.prepare (B : PreparedModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) :
  Result (core.result.Result verifier.Prepared verifier.Error)
  := do
  let a ←
    r1_wire.SemanticTranscript.impl.state aspis_coreDigest32Inst sem.transcript
  let t ← transcript.Transcript.new aspis_coreDigest32Inst hash a v.variant
  let (gamma, t1) ←
    PreparedModel.scalar B aspis_coreDigest32Inst t 27#u8 v.y1 true
  let a1 ← B.toBytes v.inactive
  let s ← lift (Array.to_slice a1)
  let (kappa, t2) ←
    PreparedModel.scalar B aspis_coreDigest32Inst t1 28#u8 s false
  let (alpha0, t3) ←
    PreparedModel.scalar B aspis_coreDigest32Inst t2 29#u8 v.round0 false
  let i ← transport.Variant.folds v.variant
  if i = 2#usize
  then
    let i1 ← 32#usize + 224#usize
    let bytes := alloc.vec.Vec.with_capacity Std.U8 i1
    let a2 ← core.option.Option.unwrap v.folded_root
    let s1 ← lift (Array.to_slice a2)
    let bytes1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes s1
    let bytes2 ←
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes1 v.round1
    let s2 := alloc.vec.Vec.deref bytes2
    let (we, t4) ←
      PreparedModel.scalar B aspis_coreDigest32Inst t3 30#u8 s2 false
    let (r, t5) ←
      B.queries aspis_coreDigest32Inst t4 31#u8
        v.final_message
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i2 ← 31#u8 + 1#u8
      let s3 ← lift (Array.to_slice (Std.Array.empty Std.U8))
      let (rho, t6) ←
        PreparedModel.scalar_k B aspis_coreDigest32Inst t5 i2 s3
      let r1 ←
        B.claim aspis_coreDigest32Inst sem v.y1 v.inactive
          gamma kappa
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        ok (core.result.Result.Ok
          {
            variant := v.variant,
            roots := sem.roots,
            gamma,
            kappa,
            alpha := (Array.make 2#usize [ alpha0, we ]),
            rho,
            queries := val,
            semantic_alpha := sem.alpha,
            z := sem.z,
            claim := val1,
            state := t6.state
          })
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          verifier.Prepared (core.convert.FromSame verifier.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        verifier.Prepared (core.convert.FromSame verifier.Error) residual
  else
    let (r, t4) ←
      B.queries aspis_coreDigest32Inst t3 30#u8
        v.final_message
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i1 ← 30#u8 + 1#u8
      let s1 ← lift (Array.to_slice (Std.Array.empty Std.U8))
      let (rho, t5) ←
        PreparedModel.scalar_k B aspis_coreDigest32Inst t4 i1 s1
      let r1 ←
        B.claim aspis_coreDigest32Inst sem v.y1 v.inactive
          gamma kappa
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        ok (core.result.Result.Ok
          {
            variant := v.variant,
            roots := sem.roots,
            gamma,
            kappa,
            alpha :=
              (Array.make 2#usize [ alpha0, aspis_core.field.WideExact.ZERO ]),
            rho,
            queries := val,
            semantic_alpha := sem.alpha,
            z := sem.z,
            claim := val1,
            state := t5.state
          })
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          verifier.Prepared (core.convert.FromSame verifier.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        verifier.Prepared (core.convert.FromSame verifier.Error) residual

def PreparedModel.entry (B : PreparedModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) :
  Result (core.result.Result verifier.Prepared verifier.Error)
  := do
  PreparedModel.prepare B aspis_coreDigest32Inst sem v hash

#print axioms PreparedModel.scalar
#print axioms PreparedModel.scalar_k
#print axioms PreparedModel.prepare
#print axioms PreparedModel.entry
end AspisR1PublicPreparation
