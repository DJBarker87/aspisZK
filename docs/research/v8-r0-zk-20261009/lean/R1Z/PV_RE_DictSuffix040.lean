import R1Z.PV_RE_DictSuffix039
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix040
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


end R1Z.PV_RE_DictSuffix040
pv_dict_congr ProverRwFull.aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
pv_dict_congr R1Z.PV_RE_DictSuffix040.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix040.continueAfter
