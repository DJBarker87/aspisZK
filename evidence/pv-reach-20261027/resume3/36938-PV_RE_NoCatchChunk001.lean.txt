import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix002
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (out : Payload (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1)) : Result (core.result.Result (alloc.vec.Vec aspis_core.field.QM31)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) := do
  let r := out
  let r1 ←
    core.result.Result.map_err
      aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1StateOnlyMaskBuildError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let i ←
      aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1
    aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d
      self hash context i val
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec aspis_core.field.QM31) (core.convert.FromSame
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual


end R1Z.PV_RE_NoCatchSuffix002
pv_no_catch_binds ProverRwFull.aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix002.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix003
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (out : Payload (aspis_core.state_only_hiding.PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT)) : Result (core.result.Result Unit
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) := do
  let i := out
  let (i1, legacy) ←
    if context.mask_layout_fingerprint = i
    then
      match context.layout_factor_fingerprint with
      | 2974012453224067339#uscalar => ok (2974012453224067339#u64, true)
      | 1731042625218380614#uscalar => ok (1731042625218380614#u64, true)
      | _ => ok (context.layout_factor_fingerprint, false)
    else ok (context.layout_factor_fingerprint, false)
  let i2 ←
    aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1
  let forest ←
    if context.mask_layout_fingerprint = i2
    then
      do
      let i3 ←
        aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1
      ok (i1 = i3)
    else ok false
  let b ←
    core.cmp.PartialEq.ne.trait_default
      aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext
      { context with layout_factor_fingerprint := i1 } self.reserved_context
  if b
  then
    ok (core.result.Result.Err
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout)
  else
    let b1 ←
      core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
        context.mask_nonce self.mask_nonce
    if b1
    then
      ok (core.result.Result.Err
        aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout)
    else
      if legacy
      then ok (core.result.Result.Ok ())
      else
        if forest
        then ok (core.result.Result.Ok ())
        else
          ok (core.result.Result.Err
            aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout)


end R1Z.PV_RE_NoCatchSuffix003
pv_no_catch_binds ProverRwFull.aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix003.continueAfter
