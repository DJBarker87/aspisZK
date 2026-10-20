import ExtractedPreparedModel
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1PublicPreparation
/-- Sampling uses the previously checked common owner. Its unused legacy claim
field is never called by this model. Current powers/cached-claim are explicit. -/
structure PreparedScratchModel.Boundaries where
  sampling : PreparedModel.Boundaries
  powers : (N : Usize) → aspis_core.field.WideExact →
    Result (Array aspis_core.field.WideExact N)
  claim : {H : Type} → aspis_core.Digest32 H → r1_semantic.Verified H → Slice U8 →
    aspis_core.field.WideExact → Array aspis_core.field.WideExact 29#usize →
    aspis_core.field.WideExact → Result (core.result.Result aspis_core.field.WideExact verifier.Error)

def PreparedScratchModel.prepare (B : PreparedScratchModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
  (g : Array aspis_core.field.WideExact 29#usize) :
  Result ((core.result.Result verifier.Prepared verifier.Error) × (Array
    aspis_core.field.WideExact 29#usize))
  := do
  let a ←
    r1_wire.SemanticTranscript.impl.state aspis_coreDigest32Inst sem.transcript
  let t ← transcript.Transcript.new aspis_coreDigest32Inst hash a v.variant
  let (gamma, t1) ←
    PreparedModel.scalar B.sampling aspis_coreDigest32Inst t 27#u8 v.y1 true
  let a1 ← B.sampling.toBytes v.inactive
  let s ← lift (Array.to_slice a1)
  let (kappa, t2) ←
    PreparedModel.scalar B.sampling aspis_coreDigest32Inst t1 28#u8 s false
  let (alpha0, t3) ←
    PreparedModel.scalar B.sampling aspis_coreDigest32Inst t2 29#u8 v.round0 false
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
      PreparedModel.scalar B.sampling aspis_coreDigest32Inst t3 30#u8 s2 false
    let (r, t5) ←
      B.sampling.queries aspis_coreDigest32Inst t4 31#u8
        v.final_message
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i2 ← 31#u8 + 1#u8
      let s3 ← lift (Array.to_slice (Std.Array.empty Std.U8))
      let (rho, t6) ←
        PreparedModel.scalar_k B.sampling aspis_coreDigest32Inst t5 i2 s3
      let g1 ← B.powers 29#usize gamma
      let r1 ←
        B.claim aspis_coreDigest32Inst sem v.y1 v.inactive g1
          kappa
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
          }, g1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            verifier.Prepared (core.convert.FromSame verifier.Error) residual
        ok (r2, g1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          verifier.Prepared (core.convert.FromSame verifier.Error) residual
      ok (r1, g)
  else
    let (r, t4) ←
      B.sampling.queries aspis_coreDigest32Inst t3 30#u8
        v.final_message
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i1 ← 30#u8 + 1#u8
      let s1 ← lift (Array.to_slice (Std.Array.empty Std.U8))
      let (rho, t5) ←
        PreparedModel.scalar_k B.sampling aspis_coreDigest32Inst t4 i1 s1
      let g1 ← B.powers 29#usize gamma
      let r1 ←
        B.claim aspis_coreDigest32Inst sem v.y1 v.inactive g1
          kappa
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
          }, g1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            verifier.Prepared (core.convert.FromSame verifier.Error) residual
        ok (r2, g1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          verifier.Prepared (core.convert.FromSame verifier.Error) residual
      ok (r1, g)

def PreparedScratchModel.entry (B : PreparedScratchModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
  (g : Array aspis_core.field.WideExact 29#usize) :
  Result ((core.result.Result verifier.Prepared verifier.Error) × (Array
    aspis_core.field.WideExact 29#usize))
  := do
  PreparedScratchModel.prepare B aspis_coreDigest32Inst sem v hash g

#print axioms PreparedScratchModel.prepare
#print axioms PreparedScratchModel.entry
end AspisR1PublicPreparation
