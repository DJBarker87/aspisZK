import LIBC_PreparedLog
import LIBC_CodeMonad
set_option autoImplicit false
noncomputable section
namespace LIBC_PreparedPrefix
open Aeneas Aeneas.Std Result AspisR1 AspisR1PublicPreparation
open NFW_PreparedControl
abbrev Effects := PreparedHashCode.preparationEffects NBA_Installed.actual NBL_QueryDictionary.boundaries
abbrev Prelude := aspis_core.field.WideExact × aspis_core.field.WideExact × aspis_core.field.WideExact × transcript.Transcript Unit × Usize
/-- Exact source prefix before the fold Vec, with full ordered digest calls. -/
def prefix (D : aspis_core.Digest32 Unit) (sem : r1_semantic.Verified Unit) (v : verifier.View) :
 PreparedHashCode.Code Prelude := do
 let state ← r1_wire.SemanticTranscript.impl.state D sem.transcript
 let t ← Effects.newTranscript D () state v.variant
 let (gamma,t1) ← Effects.scalar D t 27#u8 v.y1 true
 let bytes ← Effects.toBytes v.inactive
 let payload ← lift (Array.to_slice bytes)
 let (kappa,t2) ← Effects.scalar D t1 28#u8 payload false
 let (alpha0,t3) ← Effects.scalar D t2 29#u8 v.round0 false
 let folds ← transport.Variant.folds v.variant
 pure (gamma,kappa,alpha0,t3,folds)
/-- Source suffix; no hidden result or chosen endpoint is a parameter. -/
def tail (D : aspis_core.Digest32 Unit) (sem : r1_semantic.Verified Unit) (v : verifier.View)
 (g : Scratch) (p : Prelude) : PreparedHashCode.Code Out := do
 let (gamma,kappa,alpha0,t3,i) := p
 let effects := Effects
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
      effects.scalar D t3 30#u8 s2
        false
    let (r, t5) ←
      effects.queries D t4 31#u8
        v.final_message
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i2 ← 31#u8 + 1#u8
      let s3 ← lift (Array.to_slice (Std.Array.empty Std.U8))
      let (rho, t6) ←
        effects.rho D t5 i2 s3
      let g1 ← effects.powers 29#usize gamma
      let r1 ←
        effects.claim D sem v.y1
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
      effects.queries D t3 30#u8
        v.final_message
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i1 ← 30#u8 + 1#u8
      let s1 ← lift (Array.to_slice (Std.Array.empty Std.U8))
      let (rho, t5) ←
        effects.rho D t4 i1 s1
      let g1 ← effects.powers 29#usize gamma
      let r1 ←
        effects.claim D sem v.y1
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

theorem factor (D : aspis_core.Digest32 Unit) (sem : r1_semantic.Verified Unit) (v : verifier.View)
 (g : Scratch) :
 LIBC_PreparedLog.code D sem v () g =
 (prefix D sem v >>= tail D sem v g) := by
 unfold NBL_CohortCode.code PreparedSourceEffects.prepare prefix tail
 simp only [LIBC_CodeMonad.bind_assoc]
 rfl
#print axioms factor
end LIBC_PreparedPrefix
