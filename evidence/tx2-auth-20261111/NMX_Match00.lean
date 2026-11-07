import NMX_BindCongruence
import NMX_PdaMap
import NMX_Actual00
import NMX_Fold00
import NMX_Match01
set_option autoImplicit false
noncomputable section
namespace NMX_Match00
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_ResultSteps

/-- Actual emitted occurrence 10; complete arbitrary reply/control arms. -/
theorem e010 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_Fold00.v010 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint =
 NMX_Actual00.t010 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint := by
 unfold NMX_Fold00.v010 NMX_Actual00.t010
 unfold tryThen
 apply NMX_BindCongruence.step
 intro reply
 cases reply with
 | Err error => rfl
 | Ok unit =>
   exact NMX_Match01.e011 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e010

/-- Actual emitted occurrence 9; complete arbitrary reply/control arms. -/
theorem e009 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_Fold00.v009 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint =
 NMX_Actual00.t009 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint := by
 unfold NMX_Fold00.v009 NMX_Actual00.t009
 unfold tryThen
 apply NMX_BindCongruence.step
 intro reply
 cases reply with
 | Err error => rfl
 | Ok unit =>
   exact NMX_Match00.e010 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e009

/-- Actual emitted occurrence 8; complete arbitrary reply/control arms. -/
theorem e008 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_Fold00.v008 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint =
 NMX_Actual00.t008 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint := by
 unfold NMX_Fold00.v008 NMX_Actual00.t008
 unfold tryThen
 apply NMX_BindCongruence.step
 intro reply
 cases reply with
 | Err error => rfl
 | Ok unit =>
   exact NMX_Match00.e009 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e008

/-- Actual emitted occurrence 7; complete arbitrary reply/control arms. -/
theorem e007 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) :
 NMX_Fold00.v007 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount =
 NMX_Actual00.t007 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount := by
 unfold NMX_Fold00.v007 NMX_Actual00.t007
 apply NMX_BindCongruence.step
 intro verifierCheckpoint
 exact NMX_Match00.e008 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e007

/-- Actual emitted occurrence 6; complete arbitrary reply/control arms. -/
theorem e006 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) :
 NMX_Fold00.v006 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount =
 NMX_Actual00.t006 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount := by
 unfold NMX_Fold00.v006 NMX_Actual00.t006
 apply NMX_BindCongruence.step
 intro entryAccount
 exact NMX_Match00.e007 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount
#print axioms e006

/-- Actual emitted occurrence 5; complete arbitrary reply/control arms. -/
theorem e005 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) :
 NMX_Fold00.v005 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount =
 NMX_Actual00.t005 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount := by
 unfold NMX_Fold00.v005 NMX_Actual00.t005
 apply NMX_BindCongruence.step
 intro registryAccount
 exact NMX_Match00.e006 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount
#print axioms e005

/-- Actual emitted occurrence 4; complete arbitrary reply/control arms. -/
theorem e004 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) :
 NMX_Fold00.v004 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount =
 NMX_Actual00.t004 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount := by
 unfold NMX_Fold00.v004 NMX_Actual00.t004
 apply NMX_BindCongruence.step
 intro laneAccount
 exact NMX_Match00.e005 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount
#print axioms e004

/-- Actual emitted occurrence 3; complete arbitrary reply/control arms. -/
theorem e003 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) :
 NMX_Fold00.v003 owners ops verifier accounts pool outputLane slot proof masterAccount =
 NMX_Actual00.t003 owners ops verifier accounts pool outputLane slot proof masterAccount := by
 unfold NMX_Fold00.v003 NMX_Actual00.t003
 apply NMX_BindCongruence.step
 intro checkpointAccount
 exact NMX_Match00.e004 owners ops verifier accounts pool outputLane slot proof masterAccount checkpointAccount
#print axioms e003

/-- Actual emitted occurrence 2; complete arbitrary reply/control arms. -/
theorem e002 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) :
 NMX_Fold00.v002 owners ops verifier accounts pool outputLane slot proof =
 NMX_Actual00.t002 owners ops verifier accounts pool outputLane slot proof := by
 unfold NMX_Fold00.v002 NMX_Actual00.t002
 apply NMX_BindCongruence.step
 intro masterAccount
 exact NMX_Match00.e003 owners ops verifier accounts pool outputLane slot proof masterAccount
#print axioms e002

/-- Actual emitted occurrence 1; complete arbitrary reply/control arms. -/
theorem e001 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) :
 NMX_Fold00.v001 owners ops verifier accounts pool outputLane slot =
 NMX_Actual00.t001 owners ops verifier accounts pool outputLane slot := by
 unfold NMX_Fold00.v001 NMX_Actual00.t001
 apply NMX_BindCongruence.step
 intro proof
 exact NMX_Match00.e002 owners ops verifier accounts pool outputLane slot proof
#print axioms e001
end NMX_Match00
end
