import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue072
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.derive_private_salt_step`.
Recursive calls remain the original extracted calls. -/
def continueAfter (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (tag : Std.U8) (index : Std.U32) (salts : alloc.vec.Vec (Array Std.U8 32#usize)) (out : Payload (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt
      reserved hash context tag index)) : Result (core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
    verifier.Error) := do
  let r := out
  let r1 ←
    core.result.Result.map_err
      prover.derive_private_salt_step.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let salts1 ← alloc.vec.Vec.push salts val
    ok (core.result.Result.Ok salts1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec (Array Std.U8 32#usize)) (core.convert.FromSame
      verifier.Error) residual

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (tag : Std.U8) (index : Std.U32) (salts : alloc.vec.Vec (Array Std.U8 32#usize)) :
    prover.derive_private_salt_step (reserved := reserved) (context := context) (hash := hash) (tag := tag) (index := index) (salts := salts) =
      (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt
      reserved hash context tag index >>= fun out => continueAfter (reserved := reserved) (context := context) (hash := hash) (tag := tag) (index := index) (salts := salts) out) := by
  rw [prover.derive_private_salt_step]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (tag : Std.U8) (index : Std.U32) (salts : alloc.vec.Vec (Array Std.U8 32#usize)) (out : Payload (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt
      reserved hash context tag index))
    (h : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt
      reserved hash context tag index) = .ok out) :
    prover.derive_private_salt_step (reserved := reserved) (context := context) (hash := hash) (tag := tag) (index := index) (salts := salts) = continueAfter (reserved := reserved) (context := context) (hash := hash) (tag := tag) (index := index) (salts := salts) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (tag : Std.U8) (index : Std.U32) (salts : alloc.vec.Vec (Array Std.U8 32#usize)) (e : Error)
    (h : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt
      reserved hash context tag index) = .fail e) :
    prover.derive_private_salt_step (reserved := reserved) (context := context) (hash := hash) (tag := tag) (index := index) (salts := salts) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (tag : Std.U8) (index : Std.U32) (salts : alloc.vec.Vec (Array Std.U8 32#usize))
    (h : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt
      reserved hash context tag index) = .div) :
    prover.derive_private_salt_step (reserved := reserved) (context := context) (hash := hash) (tag := tag) (index := index) (salts := salts) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue072
