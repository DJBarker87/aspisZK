import R1Z.ProverRwQueryScan
import R1Z.PV_RunJoin_ResultPost
set_option autoImplicit false
namespace R1Z.PV_RJQ_QueryDispatch
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan
open PV_RunJoin_ResultPost
variable [ExternalTypes] [ExternalFuns]
#check List.set_cons_zero
#check List.set_cons_succ
#check List.mem_cons_self
#check UScalar.val_and
#print Array.update
#print axioms queries_finite
end R1Z.PV_RJQ_QueryDispatch
