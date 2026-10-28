import NDO_JHj_MasterPda
import NDO_JHj_MasterRegistry
import NDO_JHj_KeyComparison
import NDO_JHj_Seeds
import NDO_JHd_ReferenceSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_MasterPdaStep
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHg_World
attribute [local irreducible] e2 JHg_DataMaster.value JHg_DataForest.value JHb_DataLane.value

/-- Caller-stage computation. Native child observations remain explicit. -/
theorem source (base : Ops) (slot : U64)
    (pda : (JHd_ReferenceSlots.install base).op38 JHj_Seeds.master JHb_Programs.pool=ok (.Ok JHj_Seeds.key)) :
    JHj_MasterPda.run (JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool 3#u8 slot
      (e2.snapshot 1 384 384) (e2.snapshot 2 192 192) (e2.snapshot 3 768 768)
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) JHg_AccountValues.master JHj_Seeds.key JHj_Seeds.master=
    JHj_MasterRegistry.run (JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool 3#u8 slot
      (e2.snapshot 1 384 384) (e2.snapshot 2 192 192) (e2.snapshot 3 768 768)
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) JHg_AccountValues.master JHj_Seeds.key := by
  unfold JHj_MasterPda.run
  rw [pda,bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [JHj_KeyComparison.different,bind_tc_ok]
  simp only [Bool.false_eq_true,if_false]
  rfl
#print axioms source
end AspisR1.JHj_MasterPdaStep
end
