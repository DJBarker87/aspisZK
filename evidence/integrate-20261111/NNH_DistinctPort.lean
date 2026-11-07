import NNH_DistinctSeparated
set_option autoImplicit false
noncomputable section
namespace NNH_DistinctPort
open Aeneas Aeneas.Std AdapterRw NGL_DistinctInduction

theorem value {N : Usize} (base : Ops) (env : RSL.Env)
 (a : Array r1_pool_adapter.owned.OwnedAccount N) (small : N.val ≤ 7)
 (distinct : RSL.distinctKeys (a.val.map NNH_ModelCarrier.account)=true) :
 r1_pool_adapter.owned.require_distinct_accounts (NNH_Tx2ModelSlots.install base env) a=.ok (.Ok ()) := by
 have installed : NGL_ReadonlyModel.install (NNH_Tx2ModelSlots.install base env)=NNH_Tx2ModelSlots.install base env := rfl
 have native := NGL_DistinctInduction.source (NNH_Tx2ModelSlots.install base env) a small
 rw [installed] at native
 rw [native]
 unfold reference
 rw [NNH_DistinctModelOuter.source a small (NNH_DistinctSeparated.source a distinct) N.val 0#usize
  (by change 0+N.val=N.val; omega)]
 rfl
#print axioms value
end NNH_DistinctPort
