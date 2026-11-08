import NMX_R4_CallContext
import NMX_R4_PdaObservation
import NMX_R4_CallScript00
import NMX_Fold00
import NMX_R4_Observed01
set_option autoImplicit false
noncomputable section
namespace NMX_R4_Observed00
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_R4_CallRun NMX_R4_CallContext

theorem e010 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 observe c (NMX_R4_CallScript00.t010 c.owners (ops c) verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold00.p010 c.owners (ops c) verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) := by
 unfold NMX_R4_CallScript00.t010 NMX_Fold00.p010
 change observe c (NMX_R4_CallProgram.bind (NMX_R4_CallProgram.child (.readonlyAccount masterAccount pool)) (fun reply => NMX_R4_TryObservation.after reply (fun _unit => NMX_R4_CallScript01.t011 c.owners (ops c) verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint))) = _
 apply NMX_R4_ObservedStep.child
 intro _unit
 exact NMX_R4_Observed01.e011 c verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e010

theorem e009 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 observe c (NMX_R4_CallScript00.t009 c.owners (ops c) verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold00.p009 c.owners (ops c) verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) := by
 unfold NMX_R4_CallScript00.t009 NMX_Fold00.p009
 change observe c (NMX_R4_CallProgram.bind (NMX_R4_CallProgram.child (.checkpointGuard verifierCheckpoint verifier false)) (fun reply => NMX_R4_TryObservation.after reply (fun _unit => NMX_R4_CallScript00.t010 c.owners (ops c) verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint))) = _
 apply NMX_R4_ObservedStep.child
 intro _unit
 exact NMX_R4_Observed00.e010 c verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e009

theorem e008 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 observe c (NMX_R4_CallScript00.t008 c.owners (ops c) verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold00.p008 c.owners (ops c) verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) := by
 unfold NMX_R4_CallScript00.t008 NMX_Fold00.p008
 change observe c (NMX_R4_CallProgram.bind (NMX_R4_CallProgram.child (.readonlyBuffer proof)) (fun reply => NMX_R4_TryObservation.after reply (fun _unit => NMX_R4_CallScript00.t009 c.owners (ops c) verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint))) = _
 apply NMX_R4_ObservedStep.child
 intro _unit
 exact NMX_R4_Observed00.e009 c verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e008

theorem e007 (c : Context) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) :
 observe c (NMX_R4_CallScript00.t007 c.owners (ops c) verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold00.p007 c.owners (ops c) verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount) := by
 unfold NMX_R4_CallScript00.t007 NMX_Fold00.p007
 apply NMX_R4_ObservedStep.scalar
 intro verifierCheckpoint
 exact NMX_R4_Observed00.e008 c verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e007

theorem e006 (c : Context) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) :
 observe c (NMX_R4_CallScript00.t006 c.owners (ops c) verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold00.p006 c.owners (ops c) verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount) := by
 unfold NMX_R4_CallScript00.t006 NMX_Fold00.p006
 apply NMX_R4_ObservedStep.scalar
 intro entryAccount
 exact NMX_R4_Observed00.e007 c verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount
#print axioms e006

theorem e005 (c : Context) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) :
 observe c (NMX_R4_CallScript00.t005 c.owners (ops c) verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold00.p005 c.owners (ops c) verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount) := by
 unfold NMX_R4_CallScript00.t005 NMX_Fold00.p005
 apply NMX_R4_ObservedStep.scalar
 intro registryAccount
 exact NMX_R4_Observed00.e006 c verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount
#print axioms e005

theorem e004 (c : Context) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) :
 observe c (NMX_R4_CallScript00.t004 c.owners (ops c) verifier accounts pool outputLane slot proof masterAccount checkpointAccount) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold00.p004 c.owners (ops c) verifier accounts pool outputLane slot proof masterAccount checkpointAccount) := by
 unfold NMX_R4_CallScript00.t004 NMX_Fold00.p004
 apply NMX_R4_ObservedStep.scalar
 intro laneAccount
 exact NMX_R4_Observed00.e005 c verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount
#print axioms e004

theorem e003 (c : Context) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) :
 observe c (NMX_R4_CallScript00.t003 c.owners (ops c) verifier accounts pool outputLane slot proof masterAccount) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold00.p003 c.owners (ops c) verifier accounts pool outputLane slot proof masterAccount) := by
 unfold NMX_R4_CallScript00.t003 NMX_Fold00.p003
 apply NMX_R4_ObservedStep.scalar
 intro checkpointAccount
 exact NMX_R4_Observed00.e004 c verifier accounts pool outputLane slot proof masterAccount checkpointAccount
#print axioms e003

theorem e002 (c : Context) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) :
 observe c (NMX_R4_CallScript00.t002 c.owners (ops c) verifier accounts pool outputLane slot proof) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold00.p002 c.owners (ops c) verifier accounts pool outputLane slot proof) := by
 unfold NMX_R4_CallScript00.t002 NMX_Fold00.p002
 apply NMX_R4_ObservedStep.scalar
 intro masterAccount
 exact NMX_R4_Observed00.e003 c verifier accounts pool outputLane slot proof masterAccount
#print axioms e002

theorem e001 (c : Context) (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) :
 observe c (NMX_R4_CallScript00.t001 c.owners (ops c) verifier accounts pool outputLane slot) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold00.p001 c.owners (ops c) verifier accounts pool outputLane slot) := by
 unfold NMX_R4_CallScript00.t001 NMX_Fold00.p001
 apply NMX_R4_ObservedStep.scalar
 intro proof
 exact NMX_R4_Observed00.e002 c verifier accounts pool outputLane slot proof
#print axioms e001
end NMX_R4_Observed00
end
