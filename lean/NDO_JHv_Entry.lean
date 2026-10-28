import NDO_JHv_EntryProgramdata
import NDO_JHj_EntryDecoded
import NDO_JHj_RegistryReadonly
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHv_Entry
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHu_FixturePdaRuntime
attribute [local irreducible] JHg_World.e2 JHj_Seeds.key JHj_RegistryValue.loader

theorem source (base : Ops) (slot : U64) (runtime : FixturePdaRuntime base)
    (active : (JHd_ReferenceSlots.install base).op29 JHj_RegistryValue.entry slot=ok true) :
    JHj_EntryDecoded.run (JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool
      (JHg_World.e2.snapshot 1 384 384) JHg_AccountValues.master
      (JHg_World.e2.snapshot 4 128 256) (JHg_World.e2.snapshot 5 192 320) slot
      JHb_Programs.registry JHj_RegistryValue.loader JHj_Seeds.key JHj_RegistryValue.loader
      JHj_RegistryValue.entry=ok (.Ok ()) := by
  unfold JHj_EntryDecoded.run
  change (ok JHj_Seeds.key.to_slice >>= _) = _
  rw [bind_tc_ok]
  change (ok r1_pool_adapter.PROFILE_BINDING.to_slice >>= _) = _
  rw [bind_tc_ok]
  change (ok r1_pool_adapter.RELEASE_BINDING.to_slice >>= _) = _
  rw [bind_tc_ok]
  change (ok (Array.make 1#usize [JHj_RegistryValue.entry.bump]).to_slice >>= _) = _
  rw [bind_tc_ok]
  change (ok JHj_RegistrySeeds.entry >>= _) = _
  rw [bind_tc_ok,JHu_PdaObservations.entry base runtime,bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
    r1_pool_adapter.owned.OwnedAccount.impl.key]
  rw [JHj_RegistryReadonly.shared,bind_tc_ok]
  simp only [Bool.false_eq_true,ite_false]
  change (ok CPH_Program.verifier.to_slice >>= _) = _
  rw [bind_tc_ok]
  change (ok (Array.make 1#usize [JHj_RegistryValue.entry.programdata_bump]).to_slice >>= _) = _
  rw [bind_tc_ok]
  change (ok JHj_RegistrySeeds.verifierProgramdata >>= _) = _
  rw [bind_tc_ok]
  exact JHv_EntryProgramdata.source base slot runtime active
#print axioms source
end AspisR1.JHv_Entry
end
