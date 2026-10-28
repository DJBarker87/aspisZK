import NDO_JHj_MasterRegistry
import NDO_JHj_CheckpointRead
import NDO_JHj_Seeds
import NDO_JHd_ReferenceSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_MasterRegistryStep
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHg_World
attribute [local irreducible] e2 JHg_DataMaster.value JHg_DataForest.value JHb_DataLane.value

/-- Caller-stage computation. Native child observations remain explicit. -/
theorem source (base : Ops) (slot : U64)
    (registry : r1_pool_adapter.owned.authenticate_invariant_release_registry (JHd_ReferenceSlots.install base)
      CPH_Program.verifier JHb_Programs.pool (e2.snapshot 1 384 384) JHg_AccountValues.master
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) slot=ok (.Ok ())) :
    JHj_MasterRegistry.run (JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool 3#u8 slot
      (e2.snapshot 1 384 384) (e2.snapshot 2 192 192) (e2.snapshot 3 768 768)
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) JHg_AccountValues.master JHj_Seeds.key=
    JHj_CheckpointRead.run (JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool 3#u8 slot
      (e2.snapshot 1 384 384) (e2.snapshot 2 192 192) (e2.snapshot 3 768 768)
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) JHg_AccountValues.master JHj_Seeds.key := by
  unfold JHj_MasterRegistry.run
  rw [registry,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JHj_MasterRegistryStep
end
