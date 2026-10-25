import CurrentOriginalPreparedNativeV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedSourceEffects
open Aeneas Aeneas.Std Result ControlFlow
universe v

/-- Source child calls retain complete original types and all arguments.
These effects are not concrete source-oracle or mathematical model ports. -/
structure Effects (M : Type → Type v) where
  newTranscript : {H : Type} → aspis_core.Digest32 H → H → Array U8 32#usize → transport.Variant → M (transcript.Transcript H)
  scalar : {H : Type} → aspis_core.Digest32 H → transcript.Transcript H → U8 → Slice U8 → Bool → M (aspis_core.field.WideExact × transcript.Transcript H)
  toBytes : aspis_core.field.WideExact → M (Array U8 32#usize)
  queries : {H : Type} → aspis_core.Digest32 H → transcript.Transcript H → U8 → Slice U8 → M (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H)
  rho : {H : Type} → aspis_core.Digest32 H → transcript.Transcript H → U8 → Slice U8 → M (aspis_core.field.QM31 × transcript.Transcript H)
  powers : (N : Usize) → aspis_core.field.WideExact → M (Array aspis_core.field.WideExact N)
  claim : {H : Type} → aspis_core.Digest32 H → r1_semantic.Verified H → Slice U8 → aspis_core.field.WideExact → Array aspis_core.field.WideExact 29#usize → aspis_core.field.WideExact → M (core.result.Result aspis_core.field.WideExact verifier.Error)

def sourceEffects (B : PreparedScratchModel.Boundaries) : Effects Result where
  newTranscript := transcript.Transcript.new
  scalar := PreparedModel.scalar B.sampling
  toBytes := B.sampling.toBytes
  queries := B.sampling.queries
  rho := PreparedModel.scalar_k B.sampling
  powers := B.powers
  claim := B.claim

def prepare {M : Type → Type v} [Monad M] [MonadLiftT Result M] (effects : Effects M)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.Digest32 H)
  (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
  (g : Array aspis_core.field.WideExact 29#usize) :
  M ((core.result.Result verifier.Prepared verifier.Error) × (Array
    aspis_core.field.WideExact 29#usize))
  := do
  let a ←
    r1_wire.SemanticTranscript.impl.state aspis_coredigestDigest32Inst
      sem.transcript
  let t ←
    effects.newTranscript aspis_coredigestDigest32Inst hash a v.variant
  let (gamma, t1) ←
    effects.scalar aspis_coredigestDigest32Inst t 27#u8 v.y1 true
  let a1 ← effects.toBytes v.inactive
  let s ← lift (Array.to_slice a1)
  let (kappa, t2) ←
    effects.scalar aspis_coredigestDigest32Inst t1 28#u8 s false
  let (alpha0, t3) ←
    effects.scalar aspis_coredigestDigest32Inst t2 29#u8 
      v.round0 false
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
      effects.scalar aspis_coredigestDigest32Inst t3 30#u8 s2
        false
    let (r, t5) ←
      effects.queries aspis_coredigestDigest32Inst t4 31#u8
        v.final_message
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i2 ← 31#u8 + 1#u8
      let s3 ← lift (Array.to_slice (Std.Array.empty Std.U8))
      let (rho, t6) ←
        effects.rho aspis_coredigestDigest32Inst t5 i2 s3
      let g1 ← effects.powers 29#usize gamma
      let r1 ←
        effects.claim aspis_coredigestDigest32Inst sem v.y1
          v.inactive g1 kappa
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        pure (core.result.Result.Ok
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
        pure (r2, g1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          verifier.Prepared (core.convert.FromSame verifier.Error) residual
      pure (r1, g)
  else
    let we ← OriginalPreparedNative.zero
    let (r, t4) ←
      effects.queries aspis_coredigestDigest32Inst t3 30#u8
        v.final_message
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i1 ← 30#u8 + 1#u8
      let s1 ← lift (Array.to_slice (Std.Array.empty Std.U8))
      let (rho, t5) ←
        effects.rho aspis_coredigestDigest32Inst t4 i1 s1
      let g1 ← effects.powers 29#usize gamma
      let r1 ←
        effects.claim aspis_coredigestDigest32Inst sem v.y1
          v.inactive g1 kappa
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        pure (core.result.Result.Ok
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
            state := t5.state
          }, g1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            verifier.Prepared (core.convert.FromSame verifier.Error) residual
        pure (r2, g1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          verifier.Prepared (core.convert.FromSame verifier.Error) residual
      pure (r1, g)

/-- Full Result and returned scratch, including query rejection before scratch
replacement and claim rejection afterwards. No accepted-run hypothesis. -/
theorem source_exact (B : PreparedScratchModel.Boundaries) {H : Type}
    (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H) (view : verifier.View)
    (hash : H) (scratch : Array aspis_core.field.WideExact 29#usize) :
    prepare (sourceEffects B) D sem view hash scratch =
      OriginalPreparedNative.prepare B D sem view hash scratch := rfl

#print axioms source_exact
end AspisR1PublicPreparation.PreparedSourceEffects
