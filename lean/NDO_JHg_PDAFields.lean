import NDO_JHg_World
import JHg_AuditMaster
import JHg_AuditForest
import JHg_AuditLane
import JHg_AuditRegistry
import JHg_AuditEntry
set_option autoImplicit false
namespace AspisR1.JHg_PDAFields
open Aeneas Aeneas.Std Result
theorem master_key : (JHg_World.e2.snapshot 1 384 384).key.val=[34#u8,8#u8,198#u8,55#u8,61#u8,211#u8,19#u8,178#u8,242#u8,118#u8,165#u8,45#u8,20#u8,254#u8,147#u8,25#u8,55#u8,157#u8,211#u8,124#u8,152#u8,170#u8,59#u8,88#u8,182#u8,77#u8,252#u8,152#u8,45#u8,26#u8,82#u8,63#u8] := by unfold JHg_World.e2;rfl
#print axioms master_key
theorem master_seed : AdapterRw.r1_pool_adapter.PAIR_FOREST_MASTER_SEED.val=[97#u8,115#u8,112#u8,105#u8,115#u8,45#u8,112#u8,97#u8,105#u8,114#u8,45#u8,102#u8,111#u8,114#u8,101#u8,115#u8,116#u8,45#u8,109#u8,97#u8,115#u8,116#u8,101#u8,114#u8,45#u8,118#u8,49#u8] := by unfold AdapterRw.r1_pool_adapter.PAIR_FOREST_MASTER_SEED;rfl
#print axioms master_seed
theorem forest_key : (JHg_World.e2.snapshot 2 192 192).key.val=[196#u8,102#u8,84#u8,170#u8,104#u8,43#u8,219#u8,48#u8,186#u8,107#u8,137#u8,83#u8,94#u8,246#u8,77#u8,0#u8,95#u8,194#u8,23#u8,211#u8,45#u8,133#u8,134#u8,108#u8,194#u8,76#u8,167#u8,72#u8,207#u8,114#u8,192#u8,205#u8] := by unfold JHg_World.e2;rfl
#print axioms forest_key
theorem forest_seed : AdapterRw.r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED.val=[97#u8,115#u8,112#u8,105#u8,115#u8,45#u8,112#u8,97#u8,105#u8,114#u8,45#u8,102#u8,111#u8,114#u8,101#u8,115#u8,116#u8,45#u8,99#u8,104#u8,101#u8,99#u8,107#u8,112#u8,111#u8,105#u8,110#u8,116#u8,45#u8,118#u8,49#u8] := by unfold AdapterRw.r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED;rfl
#print axioms forest_seed
theorem lane_key : (JHg_World.e2.snapshot 3 768 768).key.val=[32#u8,73#u8,231#u8,207#u8,1#u8,77#u8,136#u8,117#u8,47#u8,206#u8,98#u8,125#u8,13#u8,237#u8,112#u8,176#u8,187#u8,122#u8,65#u8,248#u8,189#u8,141#u8,180#u8,25#u8,45#u8,142#u8,52#u8,8#u8,202#u8,78#u8,16#u8,28#u8] := by unfold JHg_World.e2;rfl
#print axioms lane_key
theorem lane_seed : AdapterRw.r1_pool_adapter.PAIR_FOREST_LANE_SEED.val=[97#u8,115#u8,112#u8,105#u8,115#u8,45#u8,112#u8,97#u8,105#u8,114#u8,45#u8,102#u8,111#u8,114#u8,101#u8,115#u8,116#u8,45#u8,108#u8,97#u8,110#u8,101#u8,45#u8,118#u8,49#u8] := by unfold AdapterRw.r1_pool_adapter.PAIR_FOREST_LANE_SEED;rfl
#print axioms lane_seed
theorem registry_key : (JHg_World.e2.snapshot 4 128 256).key.val=[255#u8,103#u8,20#u8,29#u8,19#u8,195#u8,72#u8,121#u8,184#u8,207#u8,93#u8,169#u8,153#u8,36#u8,142#u8,171#u8,200#u8,92#u8,79#u8,107#u8,186#u8,169#u8,198#u8,210#u8,115#u8,193#u8,229#u8,236#u8,239#u8,214#u8,81#u8,30#u8] := by unfold JHg_World.e2;rfl
#print axioms registry_key
theorem registry_seed : AdapterRw.r1_pool_adapter.VERIFIER_REGISTRY_V2_SEED.val=[97#u8,115#u8,112#u8,105#u8,115#u8,45#u8,118#u8,101#u8,114#u8,105#u8,102#u8,105#u8,101#u8,114#u8,45#u8,114#u8,101#u8,103#u8,105#u8,115#u8,116#u8,114#u8,121#u8,45#u8,118#u8,50#u8] := by unfold AdapterRw.r1_pool_adapter.VERIFIER_REGISTRY_V2_SEED;rfl
#print axioms registry_seed
theorem entry_key : (JHg_World.e2.snapshot 5 192 320).key.val=[17#u8,154#u8,124#u8,153#u8,113#u8,147#u8,61#u8,254#u8,52#u8,68#u8,8#u8,149#u8,99#u8,67#u8,208#u8,166#u8,22#u8,170#u8,233#u8,162#u8,174#u8,18#u8,23#u8,198#u8,192#u8,115#u8,178#u8,38#u8,251#u8,80#u8,120#u8,152#u8] := by unfold JHg_World.e2;rfl
#print axioms entry_key
theorem entry_seed : AdapterRw.r1_pool_adapter.VERIFIER_ENTRY_V2_SEED.val=[97#u8,115#u8,112#u8,105#u8,115#u8,45#u8,118#u8,101#u8,114#u8,105#u8,102#u8,105#u8,101#u8,114#u8,45#u8,101#u8,110#u8,116#u8,114#u8,121#u8,45#u8,118#u8,50#u8] := by unfold AdapterRw.r1_pool_adapter.VERIFIER_ENTRY_V2_SEED;rfl
#print axioms entry_seed
end AspisR1.JHg_PDAFields
