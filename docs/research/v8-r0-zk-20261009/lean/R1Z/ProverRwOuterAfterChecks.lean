import R1Z.ProverRwOuterCaller
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwOuterAfterChecks
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

def afterChecks
  {T0 : Type} (state_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (self : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (precommit_binding : Array Std.U8 32#usize)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (nonce_store : T0) :
  Result ((core.result.Result
    (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
    aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) × T0)
  := do
  let (b1, nonce_store1) ←
    state_only_hidingStateOnlyMaskNonceStoreInst.«reserve» nonce_store
      context.statement_digest context.mask_nonce
  if b1
  then
    let a ←
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
        U8.Insts.ZeroizeDefaultIsZeroes)) self.field_mask_entropy
    let (r, pre_reserved) ←
      aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref
        aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
        hash precommit_binding context a
        {
          statement_digest := context.statement_digest,
          mask_nonce := context.mask_nonce,
          consumed := false
        }
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      if pre_reserved.consumed
      then
        let s ← Aeneas.Std.lift (Array.to_slice precommit_binding)
        let a1 ←
          aspis_core.state_only_hiding.StateOnlyHidingContext.encode
            context
        let s1 ← Aeneas.Std.lift (Array.to_slice a1)
        let s2 ←
          zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref
            (Array.Insts.CoreConvertAsRefSlice Std.U8 32#usize)
            (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
            U8.Insts.ZeroizeDefaultIsZeroes)) self.field_mask_entropy
        let s3 ←
          Aeneas.Std.lift (Array.to_slice
            (Array.make 4#usize [
              aspis_prover.state_only_entropy.POOL_V1_SOURCE_SEED_DOMAIN,
              s, s1, s2
              ]))
        let a2 ← hash s3
        let source_mask_seed ←
          zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
            (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a2
        let _ ←
          zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize
            (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
            U8.Insts.ZeroizeDefaultIsZeroes)) self.field_mask_entropy
        ok (core.result.Result.Ok
          ({
             mask_nonce := self.mask_nonce,
             precommit_binding,
             reserved_context := context,
             leaf_salt_seed := self.leaf_salt_seed,
             source_mask_seed
           }, val), nonce_store1)
      else
        ok (core.result.Result.Err
          aspis_prover.state_only_hiding.StateOnlyMaskBuildError.ReusedMaskNonce,
          nonce_store1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets
          × aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
          (core.convert.FromSame
          aspis_prover.state_only_hiding.StateOnlyMaskBuildError)
          residual
      ok (r1, nonce_store1)
  else
    ok (core.result.Result.Err
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError.ReusedMaskNonce,
      nonce_store1)

end R1Z.ProverRwOuterAfterChecks
