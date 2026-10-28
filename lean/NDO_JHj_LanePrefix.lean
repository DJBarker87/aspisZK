import NDO_JHj_LaneDecoded
import NDO_JHj_LanePda
import NDO_JHj_LaneGuards
import NDO_JHj_Seeds
import NDO_JHd_ReferenceSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_LanePrefix
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHg_World
attribute [local irreducible] e2 JHg_DataMaster.value JHg_DataForest.value JHb_DataLane.value

/-- Caller-stage computation. Native child observations remain explicit. -/
theorem source (base : Ops) (slot : U64) :
    JHj_LaneDecoded.run (JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool 3#u8 slot
      (e2.snapshot 1 384 384) (e2.snapshot 2 192 192) (e2.snapshot 3 768 768)
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) JHg_AccountValues.master JHj_Seeds.key JHg_AccountValues.checkpoint (e2.snapshot 2 192 192).key JHg_AccountValues.lane=
    JHj_LanePda.run (JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool 3#u8 slot
      (e2.snapshot 1 384 384) (e2.snapshot 2 192 192) (e2.snapshot 3 768 768)
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) JHg_AccountValues.master JHj_Seeds.key JHg_AccountValues.checkpoint (e2.snapshot 2 192 192).key JHg_AccountValues.lane JHj_Seeds.lane := by
  unfold JHj_LaneDecoded.run
  change (ok JHj_Seeds.key >>= _) = _
  rw [bind_tc_ok,JHj_LaneGuards.master,bind_tc_ok]
  simp only [Bool.false_eq_true,if_false]
  rw [JHj_LaneGuards.lane]
  simp only [Bool.false_eq_true,if_false]
  unfold JHj_LanePda.run JHj_Seeds.lane
  simp only [JHd_ReferenceSlots.install,JHd_KeyStd.install,JGx_MagicStd.install,
    JHd_ReferenceSlots.leaves,lift,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JHj_LanePrefix
end
