import NNH_Tx2Configuration
import NNH_DistinctPort
set_option autoImplicit false
noncomputable section
namespace NNH_AuthSdkDistinct
open Aeneas Aeneas.Std AspisR1 AdapterRw NGL_DistinctInduction

theorem value {E : Type} {N : Usize} (missing : IDa_Deployed.Uninstalled E)
 (env : RSL.Env) (err : E) (reserve : NP6_StdModel.Reservation)
 (a : Array r1_pool_adapter.owned.OwnedAccount N) (small : N.val≤7)
 (distinct : RSL.distinctKeys (a.val.map NNH_ModelCarrier.account)=true) :
 r1_pool_adapter.owned.require_distinct_accounts (NNH_Tx2Configuration.sdk missing env err reserve) a=.ok (.Ok ()) := by
 have native := NGL_DistinctInduction.source (NNH_Tx2Configuration.sdk missing env err reserve) a small
 rw [NNH_Tx2Configuration.readonly] at native
 rw [native]
 unfold reference
 rw [NNH_DistinctModelOuter.source a small (NNH_DistinctSeparated.source a distinct) N.val 0#usize
  (by change 0+N.val=N.val; omega)]
 rfl
#print axioms value
end NNH_AuthSdkDistinct
