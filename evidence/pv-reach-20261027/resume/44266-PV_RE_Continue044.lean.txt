import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue044
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

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (tree_tag : Std.U8) (leaf_index : Std.U32) :
    aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt (self := self) (hash := hash) (context := context) (tree_tag := tree_tag) (leaf_index := leaf_index) =
      (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
      self context >>= fun out => continueAfter (self := self) (hash := hash) (context := context) (tree_tag := tree_tag) (leaf_index := leaf_index) out) := by
  rw [aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (tree_tag : Std.U8) (leaf_index : Std.U32) (out : Payload (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
      self context))
    (h : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
      self context) = .ok out) :
    aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt (self := self) (hash := hash) (context := context) (tree_tag := tree_tag) (leaf_index := leaf_index) = continueAfter (self := self) (hash := hash) (context := context) (tree_tag := tree_tag) (leaf_index := leaf_index) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (tree_tag : Std.U8) (leaf_index : Std.U32) (e : Error)
    (h : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
      self context) = .fail e) :
    aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt (self := self) (hash := hash) (context := context) (tree_tag := tree_tag) (leaf_index := leaf_index) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (tree_tag : Std.U8) (leaf_index : Std.U32)
    (h : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
      self context) = .div) :
    aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt (self := self) (hash := hash) (context := context) (tree_tag := tree_tag) (leaf_index := leaf_index) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue044
