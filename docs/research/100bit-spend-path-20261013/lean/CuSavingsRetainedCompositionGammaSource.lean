import CuSavingsRetainedCompositionTx1Source
set_option autoImplicit false
namespace AspisR1RhoPowerTail
open Aeneas Aeneas.Std Result
abbrev retained.old_tx1_prepare.closure (H : Type) := Unit
variable [PreparedCommon] [AspisR1CuRho.ScalarKBlocks]
/-- Existing candidate1 immutable-binder source interpretation, now on the
same source carriers as the actual RhoPrepared computation. The identical
whole claim tail is PreparedCommon.claim; no law about its output is assumed. -/
def retained.oldClaim {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (inactive gamma kappa : aspis_core.field.WideExact) :
    Result (core.result.Result aspis_core.field.WideExact verifier.Error) := do
  let table ← weights.powers 29#usize gamma
  gamma_new.prepared_claim D sem y1 inactive table kappa

def retained.oldPrepared
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) :
  Result (core.result.Result verifier.Prepared verifier.Error)
  := do
  let a ←
    r1_wire.SemanticTranscript.impl.state aspis_coreDigest32Inst sem.transcript
  let t ← transcript.Transcript.new aspis_coreDigest32Inst hash a v.variant
  let (gamma, t1) ←
    transcript.Transcript.scalar aspis_coreDigest32Inst t 27#u8 v.y1 true
  let a1 ← aspis_core.field.WideExact.to_le_bytes v.inactive
  let s ← lift (Array.to_slice a1)
  let (kappa, t2) ←
    transcript.Transcript.scalar aspis_coreDigest32Inst t1 28#u8 s false
  let (alpha0, t3) ←
    transcript.Transcript.scalar aspis_coreDigest32Inst t2 29#u8 v.round0 false
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
      transcript.Transcript.scalar aspis_coreDigest32Inst t3 30#u8 s2 false
    let (r, t5) ←
      transcript.Transcript.queries aspis_coreDigest32Inst t4 31#u8
        v.final_message
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i2 ← 31#u8 + 1#u8
      let s3 ← lift (Array.to_slice (Std.Array.empty Std.U8))
      let (rho, t6) ←
        transcript.Transcript.scalar_k aspis_coreDigest32Inst t5 i2 s3
      let r1 ←
        retained.oldClaim aspis_coreDigest32Inst sem v.y1 v.inactive
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
      transcript.Transcript.queries aspis_coreDigest32Inst t3 30#u8
        v.final_message
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i1 ← 30#u8 + 1#u8
      let s1 ← lift (Array.to_slice (Std.Array.empty Std.U8))
      let (rho, t5) ←
        transcript.Transcript.scalar_k aspis_coreDigest32Inst t4 i1 s1
      let r1 ←
        retained.oldClaim aspis_coreDigest32Inst sem v.y1 v.inactive
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
variable [AspisR1CuRho.HeapReserve] [RetainedPrefix]

def
  retained.old_tx1_prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (c : retained.old_tx1_prepare.closure H) (tupled_args : r1_wire.Error) :
  Result verifier.Error
  := do
  ok verifier.Error.Semantic

/-- Trait implementation: [aspis_r1_cu_gamma::gamma_old::tx1_prepare::{impl core::ops::function::FnOnce<(aspis_r1_cu_gamma::r1_wire::Error,), aspis_r1_cu_gamma::verifier::Error> for aspis_r1_cu_gamma::gamma_old::tx1_prepare::closure<H>}]
    Source: 'lib.rs', lines 909:84-909:102 -/
@[reducible]
def retained.old_tx1_prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError {H
  : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H) :
  core.ops.function.FnOnce (retained.old_tx1_prepare.closure H) r1_wire.Error
  verifier.Error := {
  call_once :=
    retained.old_tx1_prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
    aspis_coreDigest32Inst
}

/-- [aspis_r1_cu_gamma::gamma_old::tx1_prepare]:
    Source: 'lib.rs', lines 908:0-912:1 -/
def retained.old_tx1_prepare
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public)
  (v : verifier.View) (hash : H)
  (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result ((Array (Array aspis_core.field.QM31 29#usize)
    3#usize) × verifier.Prepared) verifier.Error)
  := do
  let r ←
    r1_semantic.verify_observed aspis_coreDigest32Inst public1 v.semantic hash
      obs
  let r1 ←
    core.result.Result.map_err
      (retained.old_tx1_prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      aspis_coreDigest32Inst) r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    verifier.mark obs verifier.Phase.Semantic
    let r2 ←
      retained.oldPrepared aspis_coreDigest32Inst val v hash
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      ok (core.result.Result.Ok (val.claims, val1))
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((Array (Array aspis_core.field.QM31 29#usize) 3#usize) ×
        verifier.Prepared) (core.convert.FromSame verifier.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      ((Array (Array aspis_core.field.QM31 29#usize) 3#usize) ×
      verifier.Prepared) (core.convert.FromSame verifier.Error) residual

/-- [aspis_r1_cu_gamma::gamma_old::tx1]:
    Source: 'lib.rs', lines 914:0-919:1
    Visibility: public -/
def retained.old_tx1
  (finish : Finish) {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8) (k : Std.Usize)
  (hash : H) (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error)
  := do
  if k > 22#usize
  then ok (core.result.Result.Err verifier.Error.Parse)
  else
    let r ← verifier.View.parse proof
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue v =>
      verifier.mark obs verifier.Phase.Parsed
      let r1 ←
        retained.old_tx1_prepare aspis_coreDigest32Inst public1 v hash obs
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let (_, p) := val
        let r2 ← verifier.Accumulator.new v.variant
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let g ← weights.powers 29#usize p.gamma
          verifier.mark obs verifier.Phase.Prepare
          finish aspis_coreDigest32Inst v p val1 g public_bytes
            proof k hash obs
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual
#print axioms retained.oldPrepared
#print axioms retained.old_tx1
end AspisR1RhoPowerTail
