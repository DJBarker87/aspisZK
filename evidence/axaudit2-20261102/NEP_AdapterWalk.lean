import Lean
import AdapterRwTypes
import AdapterRwModel
import AdapterRwCuts
import NEP_WALKER
run_cmd NEP.audit `AdapterRw.r1_pool_adapter.owned.stage2_owned "NEP_Adapter"
#print axioms AdapterRw.r1_pool_adapter.owned.stage2_owned
