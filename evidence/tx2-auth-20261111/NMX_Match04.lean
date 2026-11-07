import NMX_BindCongruence
import NMX_PdaMap
import NMX_Actual04
import NMX_Fold04
import NMX_Match05
set_option autoImplicit false
noncomputable section
namespace NMX_Match04
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_ResultSteps

/-- Actual emitted occurrence 50; complete arbitrary reply/control arms. -/
theorem e050 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (wrongLanePda : Bool) :
 NMX_Fold04.v050 owners ops master masterKey checkpoint checkpointKey lane laneKey wrongLanePda =
 NMX_Actual04.t050 owners ops master.payload masterKey checkpoint.payload checkpointKey lane.payload laneKey wrongLanePda := by
 unfold NMX_Fold04.v050 NMX_Actual04.t050
 by_cases condition : (wrongLanePda) = true
 · simp only [condition,↓reduceIte]
 · simp only [condition,↓reduceIte]
   exact NMX_Match05.e051 owners ops master masterKey checkpoint checkpointKey lane laneKey
#print axioms e050

/-- Actual emitted occurrence 49; complete arbitrary reply/control arms. -/
theorem e049 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (derivedLane : solana_pubkey.Pubkey) (laneKey : solana_pubkey.Pubkey) :
 NMX_Fold04.v049 owners ops master masterKey checkpoint checkpointKey lane derivedLane laneKey =
 NMX_Actual04.t049 owners ops master.payload masterKey checkpoint.payload checkpointKey lane.payload derivedLane laneKey := by
 unfold NMX_Fold04.v049 NMX_Actual04.t049
 apply NMX_BindCongruence.step
 intro wrongLanePda
 exact NMX_Match04.e050 owners ops master masterKey checkpoint checkpointKey lane laneKey wrongLanePda
#print axioms e049

/-- Actual emitted occurrence 48; complete arbitrary reply/control arms. -/
theorem e048 (owners : Owners) (ops : Ops) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (derivedLane : solana_pubkey.Pubkey) :
 NMX_Fold04.v048 owners ops laneAccount master masterKey checkpoint checkpointKey lane derivedLane =
 NMX_Actual04.t048 owners ops laneAccount master.payload masterKey checkpoint.payload checkpointKey lane.payload derivedLane := by
 unfold NMX_Fold04.v048 NMX_Actual04.t048
 apply NMX_BindCongruence.step
 intro laneKey
 exact NMX_Match04.e049 owners ops master masterKey checkpoint checkpointKey lane derivedLane laneKey
#print axioms e048

/-- Actual emitted occurrence 47; complete arbitrary reply/control arms. -/
theorem e047 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneSeeds : Slice (Slice U8)) :
 NMX_Fold04.v047 owners ops pool laneAccount master masterKey checkpoint checkpointKey lane laneSeeds =
 NMX_Actual04.t047 owners ops pool laneAccount master.payload masterKey checkpoint.payload checkpointKey lane.payload laneSeeds := by
 unfold NMX_Fold04.v047 NMX_Actual04.t047
 rw [NMX_PdaMap.try_bind]
 apply NMX_BindCongruence.step
 intro reply
 cases reply with
 | Err error => rfl
 | Ok derivedLane =>
   exact NMX_Match04.e048 owners ops laneAccount master masterKey checkpoint checkpointKey lane derivedLane
#print axioms e047

/-- Actual emitted occurrence 46; complete arbitrary reply/control arms. -/
theorem e046 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) :
 NMX_Fold04.v046 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane =
 NMX_Actual04.t046 owners ops pool outputLane laneAccount master.payload masterKey checkpoint.payload checkpointKey lane.payload := by
 unfold NMX_Fold04.v046 NMX_Actual04.t046
 apply NMX_BindCongruence.step
 intro laneMasterSeed
 let laneIdSeed := Array.to_slice (Array.make 1#usize [outputLane])
 let laneBump := Array.to_slice (Array.make 1#usize [lane.payload.bump])
 let laneSeeds := Array.to_slice (Array.make 4#usize [
   r1_pool_adapter.PAIR_FOREST_LANE_SEED,laneMasterSeed,laneIdSeed,laneBump])
 exact NMX_Match04.e047 owners ops pool laneAccount master masterKey checkpoint checkpointKey lane laneSeeds
#print axioms e046

/-- Actual emitted occurrence 45; complete arbitrary reply/control arms. -/
theorem e045 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) :
 NMX_Fold04.v045 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane =
 NMX_Actual04.t045 owners ops pool outputLane laneAccount master.payload masterKey checkpoint.payload checkpointKey lane.payload := by
 unfold NMX_Fold04.v045 NMX_Actual04.t045
 by_cases condition : ((lane.payload.lane_id != outputLane)) = true
 · simp only [condition,↓reduceIte]
 · simp only [condition,↓reduceIte]
   exact NMX_Match04.e046 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane
#print axioms e045

/-- Actual emitted occurrence 44; complete arbitrary reply/control arms. -/
theorem e044 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (wrongLaneMaster : Bool) :
 NMX_Fold04.v044 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane wrongLaneMaster =
 NMX_Actual04.t044 owners ops pool outputLane laneAccount master.payload masterKey checkpoint.payload checkpointKey lane.payload wrongLaneMaster := by
 unfold NMX_Fold04.v044 NMX_Actual04.t044
 by_cases condition : (wrongLaneMaster) = true
 · simp only [condition,↓reduceIte]
 · simp only [condition,↓reduceIte]
   exact NMX_Match04.e045 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane
#print axioms e044

/-- Actual emitted occurrence 43; complete arbitrary reply/control arms. -/
theorem e043 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneMasterBytes : Array U8 32#usize) :
 NMX_Fold04.v043 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane laneMasterBytes =
 NMX_Actual04.t043 owners ops pool outputLane laneAccount master.payload masterKey checkpoint.payload checkpointKey lane.payload laneMasterBytes := by
 unfold NMX_Fold04.v043 NMX_Actual04.t043
 apply NMX_BindCongruence.step
 intro wrongLaneMaster
 exact NMX_Match04.e044 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane wrongLaneMaster
#print axioms e043

/-- Actual emitted occurrence 42; complete arbitrary reply/control arms. -/
theorem e042 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) :
 NMX_Fold04.v042 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane =
 NMX_Actual04.t042 owners ops pool outputLane laneAccount master.payload masterKey checkpoint.payload checkpointKey lane.payload := by
 unfold NMX_Fold04.v042 NMX_Actual04.t042
 apply NMX_BindCongruence.step
 intro laneMasterBytes
 exact NMX_Match04.e043 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane laneMasterBytes
#print axioms e042

/-- Actual emitted occurrence 41; complete arbitrary reply/control arms. -/
theorem e041 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (laneBytes : Slice U8) :
 NMX_Fold04.v041 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey laneBytes =
 NMX_Actual04.t041 owners ops pool outputLane laneAccount master.payload masterKey checkpoint.payload checkpointKey laneBytes := by
 unfold NMX_Fold04.v041 NMX_Actual04.t041
 unfold tryThen
 apply NMX_BindCongruence.step
 intro reply
 cases reply with
 | Err error => rfl
 | Ok value =>
   let lane : Box Lane := ⟨owners.lane,value⟩
   exact NMX_Match04.e042 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane
#print axioms e041
end NMX_Match04
end
