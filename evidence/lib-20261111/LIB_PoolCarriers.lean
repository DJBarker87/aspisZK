import LIB_Env
import NMS_R2Tail242
import NND_CheckpointCarrier
import NND_EntryV2Carrier
set_option autoImplicit false
namespace LIB_PoolCarriers
abbrev Request := NMS_R2Tail242.Request
abbrev Statement := NMS_R2Tail242.Statement
abbrev Afterstate := NMS_R2Tail242.Candidate
/-- Shared emitted-copy identities: every consumer uses this exact carrier. -/
def request (x : Request) : Request := x
def statement (x : Statement) : Statement := x
def afterstate (x : Afterstate) : Afterstate := x
abbrev master := NND_Carrier.master
abbrev checkpoint := NND_Carrier.checkpoint
abbrev policy := NND_Carrier.policy
abbrev registryV1 := NND_Carrier.registryV1
abbrev registryV2 := NND_Carrier.registryV2
abbrev entryV1 := NND_Carrier.entryV1
abbrev entryV2 := NND_Carrier.entryV2
theorem master_exact (x : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) :
    master x = NMS_R2N_RSLPoolCarriers.master x := rfl
theorem checkpoint_exact (x : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1) :
    checkpoint x = NMS_R2N_RSLPoolCarriers.checkpoint x := rfl
theorem policy_exact (x : AdapterRw.aspis_statement.pool_v1.format.VerifierPolicyV1) :
    policy x = NMS_R2N_RSLPoolCarriers.policy x := rfl
theorem request_exact (x : Request) : request x = x := rfl
theorem statement_exact (x : Statement) : statement x = x := rfl
theorem afterstate_exact (x : Afterstate) : afterstate x = x := rfl
#print axioms request_exact
#print axioms statement_exact
#print axioms afterstate_exact
#print axioms master_exact
#print axioms checkpoint_exact
#print axioms policy_exact
end LIB_PoolCarriers
