import R1Z.PV_RE_DictSuffix046
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix047
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.Commitment.fill_opening`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : host_commitment.Commitment) (u : aspis_core.r0.domain.FibreIndex) (out : aspis_core.r0.wire.FibreOpening) (pvBoundValue : Payload (host_commitment.fill_opening_values self u out.values 0#usize)) : Result aspis_core.r0.wire.FibreOpening := do
  let a := pvBoundValue
  let path ← host_commitment.opening_path self.time
  let a1 := Array.repeat 32#usize 0#u8
  let a2 := Array.repeat 7#usize a1
  let a3 := Array.repeat 6#usize a2
  let a4 ← Array.update out.paths path a3
  ok { values := a, paths := a4 }


end R1Z.PV_RE_DictSuffix047
pv_dict_congr ProverRwFull.host_commitment.Commitment.fill_opening
pv_dict_congr R1Z.PV_RE_DictSuffix047.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.host_commitment.Commitment.fill_opening
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix047.continueAfter
