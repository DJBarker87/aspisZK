import PCB_GetterRef.Funs
import NLG_COMBINED_IMPORT
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCB_GetterLaws

theorem tree (x : PCB_GetterRef.Validated) :
    PCB_GetterRef.tree_ref x = ok x.inner := by rfl

theorem deref_tree (x : PCB_GetterRef.Validated) :
    PCB_GetterRef.deref_ref x = ok x.inner := by rfl

theorem seed {P : Type} (x : PCB_GetterRef.Plan P) :
    PCB_GetterRef.seed_ref x = ok x.seed := by rfl

theorem value (x : PCB_GetterRef.Auth
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1) :
    PCB_GetterRef.value_ref x = ok x.value := by rfl

theorem state {P S : Type} (x : PCB_GetterRef.Canonical P S) :
    PCB_GetterRef.state_ref x = ok x.state := by rfl

#print axioms tree
#print axioms deref_tree
#print axioms seed
#print axioms value
#print axioms state
end PCB_GetterLaws
