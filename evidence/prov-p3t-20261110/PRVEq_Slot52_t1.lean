import Aeneas
import NNH_HostCtx
import NOC_Run5bHost
import AspisR1AdapterReconstruct.Funs
import PRVEq_AspisR1AdapterReconstruct_Funs
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1
set_option autoImplicit false
noncomputable section
namespace PCVV_Slot52

/-- The frozen emission (fresh PCWE_E001, overflow ON) of `reconstruct_asq8_statement`. -/
abbrev fresh := @PRVFresh_AspisR1AdapterReconstruct_Funs.r1_pool_adapter.reconstruct_asq8_statement

/-- Slot op52 at the corrected seed, generic in the context: the deployed wrapper is carrier conversion of the arguments,
the frozen emission, and carrier conversion of the result. The gate definition is equated to the frozen emission by
PRVEq.AspisR1AdapterReconstruct.Funs.r1_pool_adapter.reconstruct_asq8_statement (unconditional). -/
theorem slot52 {W Tx : Type} (c : AspisR1.NNH_HostCtx.Ctx W Tx) (request accounts candidate : _) :
    (AspisR1.NOC_HostCtx.sdk c).op52 request accounts candidate =
      (do let result ← fresh (JHf_Carrier.toRequest request) (JHf_Carrier.toAuthenticatedAsq8Accounts accounts)
              (JHf_Carrier.toPoolV1PairVerifiedAfterstateV1 candidate)
          match result with
          | core.result.Result.Ok statement =>
            ok (core.result.Result.Ok (JHf_Carrier.fromPoolV1PairForestTerminalStatementV1 statement))
          | core.result.Result.Err error =>
            ok (core.result.Result.Err (NFY_JHf_ProgramErrorCarrier.fromRaw error))) := by
  show (do let result ← AspisR1AdapterReconstruct.r1_pool_adapter.reconstruct_asq8_statement (JHf_Carrier.toRequest request)
              (JHf_Carrier.toAuthenticatedAsq8Accounts accounts) (JHf_Carrier.toPoolV1PairVerifiedAfterstateV1 candidate)
           match result with
           | core.result.Result.Ok statement =>
             ok (core.result.Result.Ok (JHf_Carrier.fromPoolV1PairForestTerminalStatementV1 statement))
           | core.result.Result.Err error =>
             ok (core.result.Result.Err (NFY_JHf_ProgramErrorCarrier.fromRaw error))) = _
  rw [← PRVEq.AspisR1AdapterReconstruct.Funs.r1_pool_adapter.reconstruct_asq8_statement]

#print axioms slot52
end PCVV_Slot52
