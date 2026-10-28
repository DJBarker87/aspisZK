import NDO_JHj_EntryRead
import NDO_JHj_EntryDecoded
import NDO_JHj_RegistryReads
import NDO_JHj_RegistryValue
import NDO_JHd_ReferenceSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_EntryReadStep
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHg_World
attribute [local irreducible] e2 JHb_DataRegistry.value JHb_DataEntry.value

/-- Exact real account read followed by the explicit native decoder observation. -/
theorem source (base : Ops) (slot : U64)
    (decoded : (JHd_ReferenceSlots.install base).op34 JHb_DataEntry.value=ok (.Ok JHj_RegistryValue.entry)) :
    JHj_EntryRead.run (JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool
      (e2.snapshot 1 384 384) JHg_AccountValues.master
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) slot JHb_Programs.registry JHj_RegistryValue.loader JHj_Seeds.key JHj_RegistryValue.loader=
    JHj_EntryDecoded.run (JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool
      (e2.snapshot 1 384 384) JHg_AccountValues.master
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) slot JHb_Programs.registry JHj_RegistryValue.loader JHj_Seeds.key JHj_RegistryValue.loader JHj_RegistryValue.entry := by
  unfold JHj_EntryRead.run
  rw [JHj_RegistryReads.entry,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [decoded,bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JHj_EntryReadStep
end
