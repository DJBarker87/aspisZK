import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix063
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error.call_once`.
Recursive calls remain the original extracted calls. -/
def continueAfter {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F) (c : host_sumcheck.prove_sumcheck_round.closure H F) (i : Std.Usize) (out : Payload (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultQM31Error.call_mut
      aspis_coredigestDigest32Inst OracleInst c i)) : Result (core.result.Result aspis_core.field.QM31 r1_wire.Error) := do
  let (r, _) := out
  ok r


end R1Z.PV_RE_NoCatchSuffix063
pv_no_catch_binds ProverRwFull.host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultQM31Error.call_once
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix063.continueAfter
