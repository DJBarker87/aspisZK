import NDO_JHj_CheckpointDecoded
import NDO_JHj_CheckpointPda
import NDO_JHj_CheckpointGuards
import NDO_JHj_Seeds
import NDO_JHd_ReferenceSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_CheckpointPrefix
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHg_World
attribute [local irreducible] e2 JHg_DataMaster.value JHg_DataForest.value JHb_DataLane.value

/-- Caller-stage computation. Native child observations remain explicit. -/
theorem source (base : Ops) (slot : U64) :
    JHj_CheckpointDecoded.run (JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool 3#u8 slot
      (e2.snapshot 1 384 384) (e2.snapshot 2 192 192) (e2.snapshot 3 768 768)
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) JHg_AccountValues.master JHj_Seeds.key JHg_AccountValues.checkpoint=
    JHj_CheckpointPda.run (JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool 3#u8 slot
      (e2.snapshot 1 384 384) (e2.snapshot 2 192 192) (e2.snapshot 3 768 768)
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) JHg_AccountValues.master JHj_Seeds.key JHg_AccountValues.checkpoint JHj_Seeds.checkpoint := by
  unfold JHj_CheckpointDecoded.run
  change (ok JHj_Seeds.key >>= _) = _
  rw [bind_tc_ok,JHj_CheckpointGuards.master,bind_tc_ok]
  simp only [Bool.false_eq_true,if_false]
  rw [JHj_CheckpointGuards.domain,bind_tc_ok]
  simp only [Bool.false_eq_true,if_false]
  unfold JHj_CheckpointPda.run JHj_Seeds.checkpoint
  simp only [JHd_ReferenceSlots.install,JHd_KeyStd.install,JGx_MagicStd.install,
    JHd_ReferenceSlots.leaves,lift,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JHj_CheckpointPrefix
end
