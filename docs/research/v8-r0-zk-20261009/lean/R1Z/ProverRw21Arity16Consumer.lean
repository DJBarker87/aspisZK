import R1Z.ProverRw21Arity16Reference
import R1Z.ProverRw21Arity16NoPole
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21Arity16Consumer
open Aeneas Aeneas.Std Result ProverRwFull ProverRw21Arity16Reference
variable [ExternalTypes]

/-- Exact emitted endpoint consumer with a visibly retained native binding law.
The concrete P6/context identity is supplied, not re-assumed. -/
theorem endpoint (ops : ExternalFuns) (source : Source16 ops) :
    @host_semantic.copy_endpoint_values _ (ProverRw18ContextJoin.original ops) =
      @host_semantic.copy_endpoint_values _ (ProverRw18ContextJoin.owned ops) :=
  ProverRw21Arity16Endpoint.function (PV_CurrentScaleInstall.selected ops)
    ops.op223 PV_RW_CompressClosed.owned (owned ops source)

theorem no_pole (ops : ExternalFuns) (source : Source16 ops) :
    @host_semantic.no_pole _ (ProverRw18ContextJoin.original ops) =
      @host_semantic.no_pole _ (ProverRw18ContextJoin.owned ops) :=
  ProverRw21Arity16NoPole.no_pole (PV_CurrentScaleInstall.selected ops)
    ops.op223 PV_RW_CompressClosed.owned (owned ops source)

#print axioms endpoint
#print axioms no_pole
end R1Z.ProverRw21Arity16Consumer
