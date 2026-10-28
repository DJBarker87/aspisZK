import NDO_JHv_EntryChecks
import NDO_JHj_EntryProgramdata
import NDO_JHu_PdaObservations
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHv_EntryProgramdata
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHu_FixturePdaRuntime
attribute [local irreducible] JHg_World.e2 JHj_Seeds.key JHj_RegistryValue.loader

theorem source (base : Ops) (slot : U64) (runtime : FixturePdaRuntime base)
    (active : (JHd_ReferenceSlots.install base).op29 JHj_RegistryValue.entry slot=ok true) :
    JHj_EntryProgramdata.run (JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool
      (JHg_World.e2.snapshot 1 384 384) JHg_AccountValues.master
      (JHg_World.e2.snapshot 4 128 256) (JHg_World.e2.snapshot 5 192 320) slot
      JHb_Programs.registry JHj_RegistryValue.loader JHj_Seeds.key JHj_RegistryValue.loader
      JHj_RegistryValue.entry JHj_RegistrySeeds.verifierProgramdata=ok (.Ok ()) := by
  unfold JHj_EntryProgramdata.run
  rw [JHu_PdaObservations.verifierProgramdata base runtime,bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  exact JHv_EntryChecks.source base slot active
#print axioms source
end AspisR1.JHv_EntryProgramdata
end
