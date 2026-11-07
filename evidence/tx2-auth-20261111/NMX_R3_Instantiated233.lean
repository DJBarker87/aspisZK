import NMX_R2_NativeCanonical
import NMX_R2_RepresentedFold
import NMX_R3_LaneInstance
import NMX_R3_RegistryRoot
import NMX_R3_RegistryArguments
import LIBB_PoolLib
set_option autoImplicit false
noncomputable section
namespace NMX_R3_Instantiated233
open Aeneas Aeneas.Std AdapterRw NMX_SourceModel NMX_R2_Carrier

/-- The frozen fold's two selected decoders ARE module8's supplied decoders. -/
theorem library : NMX_R2_DecoderLibrary.install LIBB_PoolLib.library = LIBB_PoolLib.library := rfl

theorem registry_packet (allocations : RSL.TX2_234.Args → RSL.Env → Nat → Bool) :
 RSL.TX2_234.RowSpec_234 (NMX_R2_DecoderLibrary.install LIBB_PoolLib.library)
  LIBB_PoolLib.deployed (NMX_R3_RegistryRoot.authenticate allocations) := by
 rw [library]
 exact NMX_R3_RegistryRoot.root allocations

/-- Exactly the frozen NativeCanonical.fold, with BOTH complete child packets
and the supplied module8 instance installed. No child-law parameter survives. -/
theorem native (owners : Owners) (alloc : NMX_R2_NativeExecution.Allocations) (failure : Error)
 (laneAllocation : RSL.Bytes → RSL.Env → Bool)
 (registryAllocation : RSL.TX2_234.Args → RSL.Env → Nat → Bool)
 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (env : RSL.Env) :
 RSL.TX2_233.Ref LIBB_PoolLib.library LIBB_PoolLib.deployed
  ⟨key verifier,accounts.val.map account,key pool,byte outputLane,long slot⟩ env
  (NMX_R2_NativeExecution.run owners alloc failure
   (NMX_R3_LaneInstance.native owners.lane laneAllocation)
   (NMX_R2_CanonicalChildren.registry (NMX_R3_RegistryRoot.authenticate registryAllocation)) env
   (NMX_R2_Skeleton.auth verifier accounts pool outputLane slot)) := by
 have h := NMX_R2_NativeCanonical.fold owners alloc failure
  (NMX_R3_LaneInstance.native owners.lane laneAllocation)
  (NMX_R3_RegistryRoot.authenticate registryAllocation) LIBB_PoolLib.library LIBB_PoolLib.deployed
  (NMX_R3_LaneInstance.packet owners.lane laneAllocation) (registry_packet registryAllocation)
  verifier accounts pool outputLane slot env
 rw [library] at h
 exact h

/-- Exactly the frozen represented fold. Its explicit Rust-representation
bounds are retained as representation facts, never a new RowSpec domain. -/
theorem represented (owners : Owners) (alloc : NMX_R2_NativeExecution.Allocations) (failure : Error)
 (laneAllocation : RSL.Bytes → RSL.Env → Bool)
 (registryAllocation : RSL.TX2_234.Args → RSL.Env → Nat → Bool)
 (a : RSL.TX2_233.Args) (represented : NMX_R2_ArgsReify.Bounds a) (env : RSL.Env) :
 RSL.TX2_233.Ref LIBB_PoolLib.library LIBB_PoolLib.deployed a env
  (let native := NMX_R2_ArgsReify.reify a represented
   NMX_R2_NativeExecution.run owners alloc failure
    (NMX_R3_LaneInstance.native owners.lane laneAllocation)
    (NMX_R2_CanonicalChildren.registry (NMX_R3_RegistryRoot.authenticate registryAllocation)) env
    (NMX_R2_Skeleton.auth native.program native.accounts native.pool native.lane native.slot)) := by
 have h := NMX_R2_RepresentedFold.fold owners alloc failure
  (NMX_R3_LaneInstance.native owners.lane laneAllocation)
  (NMX_R3_RegistryRoot.authenticate registryAllocation) LIBB_PoolLib.library LIBB_PoolLib.deployed
  (NMX_R3_LaneInstance.packet owners.lane laneAllocation) (registry_packet registryAllocation) a represented env
 rw [library] at h
 exact h
#print axioms library
#print axioms registry_packet
#print axioms native
#print axioms represented
end NMX_R3_Instantiated233
end
