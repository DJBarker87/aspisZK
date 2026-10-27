import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue045
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (expected_factor_fingerprint : Std.U64) (active_masks : Array Std.U16 64#usize) (out : Payload (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
      self context)) : Result (core.result.Result (alloc.vec.Vec aspis_core.field.QM31)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) := do
  let r := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    if context.layout_factor_fingerprint != expected_factor_fingerprint
    then
      ok (core.result.Result.Err
        aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout)
    else
      let attempt_binding ←
        aspis_prover.state_only_entropy.pool_v1_private_attempt_binding hash
          self.precommit_binding context
      let s ← Aeneas.Std.lift (Array.to_slice attempt_binding)
      let s1 ←
        zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref
          (Array.Insts.CoreConvertAsRefSlice Std.U8 32#usize)
          (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) self.source_mask_seed
      let s2 ←
        Aeneas.Std.lift (Array.to_slice
          (Array.make 3#usize [
            aspis_prover.state_only_entropy.POOL_V1_D_SEED_DOMAIN, s, s1
            ]))
      let a ← hash s2
      let expander ←
        aspis_prover.state_only_entropy.Profile21SourceExpander.new hash a
      let (r1, _) ← aspis_prover.state_only_entropy.sample_source_d expander
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let active ←
          aspis_prover.state_only_entropy.source_active_flags active_masks
        let (s3, deref_mut_back) ← Aeneas.Std.lift (alloc.vec.Vec.deref_mut val)
        let (r2, s4) ←
          aspis_prover.state_only_entropy.balance_source_d s3 active
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let v := deref_mut_back s4
          let (v1, _) ←
            core.mem.take (alloc.vec.Vec.Insts.CoreDefaultDefault
              aspis_core.field.QM31) v
          ok (core.result.Result.Ok v1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec aspis_core.field.QM31) (core.convert.FromSame
            aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec aspis_core.field.QM31) (core.convert.FromSame
          aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec aspis_core.field.QM31) (core.convert.FromSame
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (expected_factor_fingerprint : Std.U64) (active_masks : Array Std.U16 64#usize) :
    aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d (self := self) (hash := hash) (context := context) (expected_factor_fingerprint := expected_factor_fingerprint) (active_masks := active_masks) =
      (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
      self context >>= fun out => continueAfter (self := self) (hash := hash) (context := context) (expected_factor_fingerprint := expected_factor_fingerprint) (active_masks := active_masks) out) := by
  rw [aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (expected_factor_fingerprint : Std.U64) (active_masks : Array Std.U16 64#usize) (out : Payload (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
      self context))
    (h : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
      self context) = .ok out) :
    aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d (self := self) (hash := hash) (context := context) (expected_factor_fingerprint := expected_factor_fingerprint) (active_masks := active_masks) = continueAfter (self := self) (hash := hash) (context := context) (expected_factor_fingerprint := expected_factor_fingerprint) (active_masks := active_masks) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (expected_factor_fingerprint : Std.U64) (active_masks : Array Std.U16 64#usize) (e : Error)
    (h : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
      self context) = .fail e) :
    aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d (self := self) (hash := hash) (context := context) (expected_factor_fingerprint := expected_factor_fingerprint) (active_masks := active_masks) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (expected_factor_fingerprint : Std.U64) (active_masks : Array Std.U16 64#usize)
    (h : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
      self context) = .div) :
    aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d (self := self) (hash := hash) (context := context) (expected_factor_fingerprint := expected_factor_fingerprint) (active_masks := active_masks) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue045
