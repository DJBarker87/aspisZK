import XRy_PowersPublic
open Aeneas Aeneas.Std Result
open XRn_Join_Release XRo_Join_Carriers
set_option autoImplicit false
noncomputable section
namespace XRy_NarrowPrepare

/- The emitted prepare body, with only excluded low_base_p_digits abstracted
through the already checked scalar callback. Powers and cached claim stay raw. -/
def prepare (low : XRq_SamplerInterface.Low)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
  Result ((core.result.Result verifier.Prepared verifier.Error) × (Array
    aspis_core.field.wide_exact.WideExact 29#usize))
  := do
  let a ←
    r1_wire.SemanticTranscript.impl.state aspis_coredigestDigest32Inst
      sem.transcript
  let t ←
    transcript.Transcript.new aspis_coredigestDigest32Inst hash a v.variant
  let (gamma, t1) ←
    XRq_OrdinaryScalar.scalar low aspis_coredigestDigest32Inst t 27#u8 v.y1 true
  let a1 ← aspis_core.field.wide_exact.WideExact.to_le_bytes v.inactive
  let s ← lift (Array.to_slice a1)
  let (kappa, t2) ←
    XRq_OrdinaryScalar.scalar low aspis_coredigestDigest32Inst t1 28#u8 s false
  let (alpha0, t3) ←
    XRq_OrdinaryScalar.scalar low aspis_coredigestDigest32Inst t2 29#u8 
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
      XRq_OrdinaryScalar.scalar low aspis_coredigestDigest32Inst t3 30#u8 s2
        false
    let (r, t5) ←
      transcript.Transcript.queries aspis_coredigestDigest32Inst t4 31#u8
        v.final_message
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i2 ← 31#u8 + 1#u8
      let s3 ← lift (Array.to_slice (Std.Array.empty Std.U8))
      let (rho, t6) ←
        transcript.Transcript.scalar_k aspis_coredigestDigest32Inst t5 i2 s3
      let g1 ← weights.powers 29#usize gamma
      let r1 ←
        verifier.prepared_claim aspis_coredigestDigest32Inst sem v.y1
          v.inactive g1 kappa
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
    let we ← aspis_core.field.wide_exact.WideExact.ZERO
    let (r, t4) ←
      transcript.Transcript.queries aspis_coredigestDigest32Inst t3 30#u8
        v.final_message
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i1 ← 30#u8 + 1#u8
      let s1 ← lift (Array.to_slice (Std.Array.empty Std.U8))
      let (rho, t5) ←
        transcript.Transcript.scalar_k aspis_coredigestDigest32Inst t4 i1 s1
      let g1 ← weights.powers 29#usize gamma
      let r1 ←
        verifier.prepared_claim aspis_coredigestDigest32Inst sem v.y1
          v.inactive g1 kappa
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


theorem emitted {H : Type} (D : E.D H) (sem : E.Sem H) (v : E.View) (hash : H)
 (g : Array C.E 29#usize) :
 prepare sampler.low_base_p_digits D sem v hash g = verifier.Prepared.new D sem v hash g := rfl

theorem gamma_canonical (low : XRq_SamplerInterface.Low)
 (leaf : ∀ block, low block = AspisR1Post25Sampler.sampler.low_base_p_digits block)
 {H : Type} (D : C.D H) (before : C.T H) (after : E.T H)
 (row : U8) (payload : Slice U8) (out : C.E)
 (run : XRq_OrdinaryScalar.scalar low (ed D) (et before) row payload true = ok (out,after)) :
 XRy_WideMultiply.Canonical out := by
 have h := (XRs_ClosedCallbacks.scalar low leaf D before row payload true).symm.trans
   (congrArg (mapR (fun p => (p.1,ct p.2))) run)
 exact AspisR1ClaimPreparedBridge.scalar_candidate_gamma_canonical
   XRo_Join_Installed.actual.sampling D before (ct after) row payload out h

#print axioms emitted
#print axioms gamma_canonical
end XRy_NarrowPrepare
end
