import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue040
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (statement_digest : Array Std.U8 32#usize) (mask_nonce : Array Std.U8 32#usize) (out : Payload (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
      self statement_digest mask_nonce)) : Result (Bool ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) := do
  let (r, self1) := out
  match r with
  | core.result.Result.Ok reserved => ok (reserved, self1)
  | core.result.Result.Err error =>
    let ek ← std.io.error.Error.kind error
    ok (false, { self1 with last_error := (some ek) })

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (statement_digest : Array Std.U8 32#usize) (mask_nonce : Array Std.U8 32#usize) :
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve (self := self) (statement_digest := statement_digest) (mask_nonce := mask_nonce) =
      (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
      self statement_digest mask_nonce >>= fun out => continueAfter (self := self) (statement_digest := statement_digest) (mask_nonce := mask_nonce) out) := by
  rw [aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (statement_digest : Array Std.U8 32#usize) (mask_nonce : Array Std.U8 32#usize) (out : Payload (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
      self statement_digest mask_nonce))
    (h : (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
      self statement_digest mask_nonce) = .ok out) :
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve (self := self) (statement_digest := statement_digest) (mask_nonce := mask_nonce) = continueAfter (self := self) (statement_digest := statement_digest) (mask_nonce := mask_nonce) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (statement_digest : Array Std.U8 32#usize) (mask_nonce : Array Std.U8 32#usize) (e : Error)
    (h : (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
      self statement_digest mask_nonce) = .fail e) :
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve (self := self) (statement_digest := statement_digest) (mask_nonce := mask_nonce) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (statement_digest : Array Std.U8 32#usize) (mask_nonce : Array Std.U8 32#usize)
    (h : (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
      self statement_digest mask_nonce) = .div) :
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve (self := self) (statement_digest := statement_digest) (mask_nonce := mask_nonce) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue040
