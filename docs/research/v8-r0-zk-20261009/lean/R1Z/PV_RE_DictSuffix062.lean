import R1Z.PV_RE_DictSuffix061
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix062
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut`.
Recursive calls remain the original extracted calls. -/
def continueAfter {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F) (state : host_sumcheck.prove_sumcheck_round.closure H F) (args : Std.Usize) (out : Payload (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error.call
      aspis_coredigestDigest32Inst OracleInst state args)) : Result ((core.result.Result aspis_core.field.QM31 r1_wire.Error) ×
    (host_sumcheck.prove_sumcheck_round.closure H F)) := do
  let r := out
  ok (r, state)


end R1Z.PV_RE_DictSuffix062
pv_dict_congr ProverRwFull.host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut
pv_dict_congr R1Z.PV_RE_DictSuffix062.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix062.continueAfter
