import R1Z.PV_RE_DictSuffix041
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix042
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_entropy.Profile21SourceExpander.m31`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : aspis_prover.state_only_entropy.Profile21SourceExpander) (out : Payload (aspis_prover.state_only_entropy.Profile21SourceExpander.m31_loop self 0#i32)) : Result ((core.result.Result aspis_core.field.M31
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_prover.state_only_entropy.Profile21SourceExpander) := do
  let (self1, pending_return) := out
  match pending_return with
  | none =>
    ok (core.result.Result.Err
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError.MaskSampleExhausted,
      self1)
  | some r => ok (r, self1)


end R1Z.PV_RE_DictSuffix042
pv_dict_congr ProverRwFull.aspis_prover.state_only_entropy.Profile21SourceExpander.m31
pv_dict_congr R1Z.PV_RE_DictSuffix042.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.aspis_prover.state_only_entropy.Profile21SourceExpander.m31
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix042.continueAfter
