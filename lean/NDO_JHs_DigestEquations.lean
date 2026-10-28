import NDO_JHs_FixtureCertificates
import NDO_JHs_SHAMaster
import NDO_JHs_SHACheckpoint
import NDO_JHs_SHALane
import NDO_JHs_SHARegistry
import NDO_JHs_SHARegistryProgramdata
import NDO_JHs_SHAEntry
import NDO_JHs_SHAVerifierProgramdata
set_option autoImplicit false
namespace AspisR1.JHs_DigestEquations
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open AspisV8R19.SqueezeOracleBridge
theorem masterDigestEquation :
    JFp_SHADigest.digest (JHs_PDA.preimage JHj_Seeds.master JHb_Programs.pool) = decodeState JHj_Seeds.key := by
  unfold JFp_SHADigest.digest
  rw [JHs_Inputs.Master.native]
  change JFp_SHADigest.output (JFp_SHA256.hash JHs_SHAMaster.raw) = _
  rw [JHs_SHAMaster.checked]
  funext i
  fin_cases i <;> rfl
#print axioms masterDigestEquation
theorem checkpointDigestEquation :
    JFp_SHADigest.digest (JHs_PDA.preimage JHj_Seeds.checkpoint JHb_Programs.pool) = decodeState (JHg_World.e2.snapshot 2 192 192).key := by
  unfold JFp_SHADigest.digest
  rw [JHs_Inputs.Checkpoint.native]
  change JFp_SHADigest.output (JFp_SHA256.hash JHs_SHACheckpoint.raw) = _
  rw [JHs_SHACheckpoint.checked]
  funext i
  fin_cases i <;> rfl
#print axioms checkpointDigestEquation
theorem laneDigestEquation :
    JFp_SHADigest.digest (JHs_PDA.preimage JHj_Seeds.lane JHb_Programs.pool) = decodeState (JHg_World.e2.snapshot 3 768 768).key := by
  unfold JFp_SHADigest.digest
  rw [JHs_Inputs.Lane.native]
  change JFp_SHADigest.output (JFp_SHA256.hash JHs_SHALane.raw) = _
  rw [JHs_SHALane.checked]
  funext i
  fin_cases i <;> rfl
#print axioms laneDigestEquation
theorem registryDigestEquation :
    JFp_SHADigest.digest (JHs_PDA.preimage JHj_RegistrySeeds.registry JHb_Programs.registry) = decodeState (JHg_World.e2.snapshot 4 128 256).key := by
  unfold JFp_SHADigest.digest
  rw [JHs_Inputs.Registry.native]
  change JFp_SHADigest.output (JFp_SHA256.hash JHs_SHARegistry.raw) = _
  rw [JHs_SHARegistry.checked]
  funext i
  fin_cases i <;> rfl
#print axioms registryDigestEquation
theorem registryProgramdataDigestEquation :
    JFp_SHADigest.digest (JHs_PDA.preimage JHj_RegistrySeeds.registryProgramdata JHj_RegistryValue.loader) = decodeState JHj_RegistryValue.registryProgramdata := by
  unfold JFp_SHADigest.digest
  rw [JHs_Inputs.RegistryProgramdata.native]
  change JFp_SHADigest.output (JFp_SHA256.hash JHs_SHARegistryProgramdata.raw) = _
  rw [JHs_SHARegistryProgramdata.checked]
  funext i
  fin_cases i <;> rfl
#print axioms registryProgramdataDigestEquation
theorem entryDigestEquation :
    JFp_SHADigest.digest (JHs_PDA.preimage JHj_RegistrySeeds.entry JHb_Programs.registry) = decodeState (JHg_World.e2.snapshot 5 192 320).key := by
  unfold JFp_SHADigest.digest
  rw [JHs_Inputs.Entry.native]
  change JFp_SHADigest.output (JFp_SHA256.hash JHs_SHAEntry.raw) = _
  rw [JHs_SHAEntry.checked]
  funext i
  fin_cases i <;> rfl
#print axioms entryDigestEquation
theorem verifierProgramdataDigestEquation :
    JFp_SHADigest.digest (JHs_PDA.preimage JHj_RegistrySeeds.verifierProgramdata JHj_RegistryValue.loader) = decodeState JHj_RegistryValue.verifierProgramdata := by
  unfold JFp_SHADigest.digest
  rw [JHs_Inputs.VerifierProgramdata.native]
  change JFp_SHADigest.output (JFp_SHA256.hash JHs_SHAVerifierProgramdata.raw) = _
  rw [JHs_SHAVerifierProgramdata.checked]
  funext i
  fin_cases i <;> rfl
#print axioms verifierProgramdataDigestEquation
theorem realization : JHs_FixtureCertificates.SHARealization :=
  ⟨masterDigestEquation, checkpointDigestEquation, laneDigestEquation,
   registryDigestEquation, registryProgramdataDigestEquation, entryDigestEquation,
   verifierProgramdataDigestEquation⟩
#print axioms realization
end AspisR1.JHs_DigestEquations
