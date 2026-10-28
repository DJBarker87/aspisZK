import NDO_JHu_FixturePdaRuntime
import NDO_JHs_DigestEquations
import NDO_JHt_OffCurve
import NDO_JHd_ReferenceSlots
set_option autoImplicit false
namespace AspisR1.JHu_PdaObservations
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHu_FixturePdaRuntime

/-- The actual free PDA slot, using only the one explicit runtime hypothesis. -/
theorem master (base : Ops) (runtime : FixturePdaRuntime base) :
    (JHd_ReferenceSlots.install base).op38 JHj_Seeds.master JHb_Programs.pool=ok (.Ok JHj_Seeds.key) := by
  change base.op38 JHj_Seeds.master JHb_Programs.pool=_
  rw [runtime _ _ .master]
  exact JHs_FixtureCertificates.master JHs_DigestEquations.realization JHt_OffCurve.certificates
#print axioms master

/-- The actual free PDA slot, using only the one explicit runtime hypothesis. -/
theorem checkpoint (base : Ops) (runtime : FixturePdaRuntime base) :
    (JHd_ReferenceSlots.install base).op38 JHj_Seeds.checkpoint JHb_Programs.pool=ok (.Ok (JHg_World.e2.snapshot 2 192 192).key) := by
  change base.op38 JHj_Seeds.checkpoint JHb_Programs.pool=_
  rw [runtime _ _ .checkpoint]
  exact JHs_FixtureCertificates.checkpoint JHs_DigestEquations.realization JHt_OffCurve.certificates
#print axioms checkpoint

/-- The actual free PDA slot, using only the one explicit runtime hypothesis. -/
theorem lane (base : Ops) (runtime : FixturePdaRuntime base) :
    (JHd_ReferenceSlots.install base).op38 JHj_Seeds.lane JHb_Programs.pool=ok (.Ok (JHg_World.e2.snapshot 3 768 768).key) := by
  change base.op38 JHj_Seeds.lane JHb_Programs.pool=_
  rw [runtime _ _ .lane]
  exact JHs_FixtureCertificates.lane JHs_DigestEquations.realization JHt_OffCurve.certificates
#print axioms lane

/-- The actual free PDA slot, using only the one explicit runtime hypothesis. -/
theorem registry (base : Ops) (runtime : FixturePdaRuntime base) :
    (JHd_ReferenceSlots.install base).op38 JHj_RegistrySeeds.registry JHb_Programs.registry=ok (.Ok (JHg_World.e2.snapshot 4 128 256).key) := by
  change base.op38 JHj_RegistrySeeds.registry JHb_Programs.registry=_
  rw [runtime _ _ .registry]
  exact JHs_FixtureCertificates.registry JHs_DigestEquations.realization JHt_OffCurve.certificates
#print axioms registry

/-- The actual free PDA slot, using only the one explicit runtime hypothesis. -/
theorem registryProgramdata (base : Ops) (runtime : FixturePdaRuntime base) :
    (JHd_ReferenceSlots.install base).op38 JHj_RegistrySeeds.registryProgramdata JHj_RegistryValue.loader=ok (.Ok JHj_RegistryValue.registryProgramdata) := by
  change base.op38 JHj_RegistrySeeds.registryProgramdata JHj_RegistryValue.loader=_
  rw [runtime _ _ .registryProgramdata]
  exact JHs_FixtureCertificates.registryProgramdata JHs_DigestEquations.realization JHt_OffCurve.certificates
#print axioms registryProgramdata

/-- The actual free PDA slot, using only the one explicit runtime hypothesis. -/
theorem entry (base : Ops) (runtime : FixturePdaRuntime base) :
    (JHd_ReferenceSlots.install base).op38 JHj_RegistrySeeds.entry JHb_Programs.registry=ok (.Ok (JHg_World.e2.snapshot 5 192 320).key) := by
  change base.op38 JHj_RegistrySeeds.entry JHb_Programs.registry=_
  rw [runtime _ _ .entry]
  exact JHs_FixtureCertificates.entry JHs_DigestEquations.realization JHt_OffCurve.certificates
#print axioms entry

/-- The actual free PDA slot, using only the one explicit runtime hypothesis. -/
theorem verifierProgramdata (base : Ops) (runtime : FixturePdaRuntime base) :
    (JHd_ReferenceSlots.install base).op38 JHj_RegistrySeeds.verifierProgramdata JHj_RegistryValue.loader=ok (.Ok JHj_RegistryValue.verifierProgramdata) := by
  change base.op38 JHj_RegistrySeeds.verifierProgramdata JHj_RegistryValue.loader=_
  rw [runtime _ _ .verifierProgramdata]
  exact JHs_FixtureCertificates.verifierProgramdata JHs_DigestEquations.realization JHt_OffCurve.certificates
#print axioms verifierProgramdata
end AspisR1.JHu_PdaObservations
