import NDO_JHj_DecodedMaster
import NDO_JHj_MasterPdaStep
import NDO_JHj_MasterRegistryStep
import NDO_JHj_CheckpointReadStep
import NDO_JHj_CheckpointPrefix
import NDO_JHj_CheckpointPdaStep
import NDO_JHj_LaneReadStep
import NDO_JHj_LanePrefix
import NDO_JHj_LanePdaStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_Authentication
open Aeneas Aeneas.Std Result S2W_D189Wrappers
open _root_.AdapterRw
open JHg_World
attribute [local irreducible] e2 JHg_DataMaster.value JHg_DataForest.value JHb_DataLane.value

/-- Complete caller composition on retained bytes. These seven native-child
observations are still premises; this is not unconditional authentication. -/
theorem source (base : Ops) (slot : U64)
    (master : (JHd_ReferenceSlots.install base).op48 JHg_DataMaster.value=ok (.Ok JHg_AccountValues.master))
    (masterPda : (JHd_ReferenceSlots.install base).op38 JHj_Seeds.master JHb_Programs.pool=ok (.Ok JHj_Seeds.key))
    (registry : r1_pool_adapter.owned.authenticate_invariant_release_registry (JHd_ReferenceSlots.install base)
      CPH_Program.verifier JHb_Programs.pool (e2.snapshot 1 384 384) JHg_AccountValues.master
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) slot=ok (.Ok ()))
    (checkpoint : (JHd_ReferenceSlots.install base).op49 JHg_DataForest.value=ok (.Ok JHg_AccountValues.checkpoint))
    (checkpointPda : (JHd_ReferenceSlots.install base).op38 JHj_Seeds.checkpoint JHb_Programs.pool=ok (.Ok (e2.snapshot 2 192 192).key))
    (lane : (JHd_ReferenceSlots.install base).op50 JHb_DataLane.value=ok (.Ok JHg_AccountValues.lane))
    (lanePda : (JHd_ReferenceSlots.install base).op38 JHj_Seeds.lane JHb_Programs.pool=ok (.Ok (e2.snapshot 3 768 768).key)) :
    r1_pool_adapter.owned.authenticate_asq8_accounts (JHd_ReferenceSlots.install base)
      CPH_Program.verifier (e2.second secondSizes) JHb_Programs.pool 3#u8 slot=ok (.Ok JHg_AccountValues.value) := by
  rw [JHj_DecodedMaster.source base slot master,
    JHj_MasterPdaStep.source base slot masterPda,
    JHj_MasterRegistryStep.source base slot registry,
    JHj_CheckpointReadStep.source base slot checkpoint,
    JHj_CheckpointPrefix.source base slot,
    JHj_CheckpointPdaStep.source base slot checkpointPda,
    JHj_LaneReadStep.source base slot lane,
    JHj_LanePrefix.source base slot,
    JHj_LanePdaStep.source base slot lanePda]
#print axioms source
end AspisR1.JHj_Authentication
end
