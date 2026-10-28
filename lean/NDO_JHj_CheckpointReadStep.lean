import NDO_JHj_CheckpointRead
import NDO_JHj_CheckpointDecoded
import NDO_JHi_AccountReads
import NDO_JHj_Seeds
import NDO_JHd_ReferenceSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_CheckpointReadStep
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHg_World
attribute [local irreducible] e2 JHg_DataMaster.value JHg_DataForest.value JHb_DataLane.value

/-- Caller-stage computation. Native child observations remain explicit. -/
theorem source (base : Ops) (slot : U64)
    (decoded : (JHd_ReferenceSlots.install base).op49 JHg_DataForest.value=ok (.Ok JHg_AccountValues.checkpoint)) :
    JHj_CheckpointRead.run (JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool 3#u8 slot
      (e2.snapshot 1 384 384) (e2.snapshot 2 192 192) (e2.snapshot 3 768 768)
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) JHg_AccountValues.master JHj_Seeds.key=
    JHj_CheckpointDecoded.run (JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool 3#u8 slot
      (e2.snapshot 1 384 384) (e2.snapshot 2 192 192) (e2.snapshot 3 768 768)
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) JHg_AccountValues.master JHj_Seeds.key JHg_AccountValues.checkpoint := by
  unfold JHj_CheckpointRead.run
  rw [JHi_AccountReads.forest,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [decoded,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JHj_CheckpointReadStep
end
