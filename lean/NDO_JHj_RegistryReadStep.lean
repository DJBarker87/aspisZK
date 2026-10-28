import NDO_JHj_RegistryRead
import NDO_JHj_RegistryDecoded
import NDO_JHj_RegistryReads
import NDO_JHj_RegistryValue
import NDO_JHd_ReferenceSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_RegistryReadStep
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHg_World
attribute [local irreducible] e2 JHb_DataRegistry.value JHb_DataEntry.value

/-- Exact real account read followed by the explicit native decoder observation. -/
theorem source (base : Ops) (slot : U64)
    (decoded : (JHd_ReferenceSlots.install base).op33 JHb_DataRegistry.value=ok (.Ok JHj_RegistryValue.registry)) :
    JHj_RegistryRead.run (JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool
      (e2.snapshot 1 384 384) JHg_AccountValues.master
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) slot JHb_Programs.registry JHj_RegistryValue.loader=
    JHj_RegistryDecoded.run (JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool
      (e2.snapshot 1 384 384) JHg_AccountValues.master
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) slot JHb_Programs.registry JHj_RegistryValue.loader JHj_RegistryValue.registry := by
  unfold JHj_RegistryRead.run
  rw [JHj_RegistryReads.registry,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [decoded,bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JHj_RegistryReadStep
end
