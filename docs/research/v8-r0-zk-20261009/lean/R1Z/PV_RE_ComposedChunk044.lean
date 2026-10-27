import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix044
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (tree_tag : Std.U8) (leaf_index : Std.U32) (out : Payload (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
      self context)) : Result (core.result.Result (Array Std.U8 32#usize)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) := do
  let r := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let attempt_binding ←
      aspis_prover.state_only_entropy.pool_v1_private_attempt_binding hash
        self.precommit_binding context
    let s ← Aeneas.Std.lift (Array.to_slice attempt_binding)
    let s1 ← Aeneas.Std.lift (Array.to_slice self.mask_nonce)
    let s2 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ tree_tag ]))
    let a ← Aeneas.Std.lift (core.num.U32.to_le_bytes leaf_index)
    let s3 ← Aeneas.Std.lift (Array.to_slice a)
    let s4 ←
      zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref
        (Array.Insts.CoreConvertAsRefSlice Std.U8 32#usize)
        (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
        U8.Insts.ZeroizeDefaultIsZeroes)) self.leaf_salt_seed
    let s5 ←
      Aeneas.Std.lift (Array.to_slice
        (Array.make 6#usize [
          aspis_prover.state_only_entropy.LEAF_SALT_DOMAIN, s, s1, s2, s3, s4
          ]))
    let a1 ← hash s5
    ok (core.result.Result.Ok a1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Array Std.U8 32#usize) (core.convert.FromSame
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual


end R1Z.PV_RE_ComposedSuffix044
pv_composed_source_contexts ProverRwFull.aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix044.continueAfter
