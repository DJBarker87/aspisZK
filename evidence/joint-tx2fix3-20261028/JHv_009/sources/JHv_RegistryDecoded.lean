import JHv_RegistryProgramdata
import JHj_RegistryDecoded
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHv_RegistryDecoded
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHu_FixturePdaRuntime
attribute [local irreducible] JHg_World.e2 JHj_Seeds.key JHj_RegistryValue.loader

theorem source (base : Ops) (slot : U64) (runtime : FixturePdaRuntime base)
    (immutable : (JHd_ReferenceSlots.install base).op28 JHj_RegistryValue.registry=ok true)
    (unrevoked : (JHd_ReferenceSlots.install base).op27 JHj_RegistryValue.registry=ok false)
    (decoded : (JHd_ReferenceSlots.install base).op34 JHb_DataEntry.value=ok (.Ok JHj_RegistryValue.entry))
    (active : (JHd_ReferenceSlots.install base).op29 JHj_RegistryValue.entry slot=ok true) :
    JHj_RegistryDecoded.run (JHd_ReferenceSlots.install base) CPH_Program.verifier JHb_Programs.pool
      (JHg_World.e2.snapshot 1 384 384) JHg_AccountValues.master
      (JHg_World.e2.snapshot 4 128 256) (JHg_World.e2.snapshot 5 192 320) slot
      JHb_Programs.registry JHj_RegistryValue.loader JHj_RegistryValue.registry=ok (.Ok ()) := by
  unfold JHj_RegistryDecoded.run
  change (ok JHj_Seeds.key >>= _) = _
  rw [bind_tc_ok]
  change (ok JHj_Seeds.key.to_slice >>= _) = _
  rw [bind_tc_ok]
  change (ok (Array.make 1#usize [JHj_RegistryValue.registry.bump]).to_slice >>= _) = _
  rw [bind_tc_ok]
  change (ok JHj_RegistrySeeds.registry >>= _) = _
  rw [bind_tc_ok,JHu_PdaObservations.registry base runtime,bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
    r1_pool_adapter.owned.OwnedAccount.impl.key]
  rw [JHj_RegistryReadonly.shared,bind_tc_ok]
  simp only [Bool.false_eq_true,ite_false]
  change (ok JHb_Programs.registry.to_slice >>= _) = _
  rw [bind_tc_ok]
  change (ok (Array.make 1#usize [JHj_RegistryValue.registry.programdata_bump]).to_slice >>= _) = _
  rw [bind_tc_ok]
  change (ok JHj_RegistrySeeds.registryProgramdata >>= _) = _
  rw [bind_tc_ok]
  exact JHv_RegistryProgramdata.source base slot runtime immutable unrevoked decoded active
#print axioms source
end AspisR1.JHv_RegistryDecoded
end
