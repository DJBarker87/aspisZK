import R1Z.PV_RE_DictSuffix036
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix037
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.semantic_error`.
Recursive calls remain the original extracted calls. -/
def continueAfter (e : r1_wire.Error) (out : Payload (r1_wire.Error.Insts.CoreCmpPartialEqError.eq e r1_wire.Error.ActivePole)) : Result verifier.Error := do
  let b := out
  if b
  then ok verifier.Error.Rejected
  else ok verifier.Error.Semantic


end R1Z.PV_RE_DictSuffix037
pv_dict_congr ProverRwFull.prover.semantic_error
pv_dict_congr R1Z.PV_RE_DictSuffix037.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.prover.semantic_error
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix037.continueAfter
