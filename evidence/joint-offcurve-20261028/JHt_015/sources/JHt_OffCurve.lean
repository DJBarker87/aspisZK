import JHs_FixtureCertificates
import JHt_Prime
import JHt_EulerBridge
import JHt_Residues
set_option autoImplicit false
namespace AspisR1.JHt_OffCurve
open AspisV8R19.SqueezeOracleBridge
theorem fieldPrime : Nat.Prime JHs_PDA.prime := JHt_Prime.prime_57896044618658097711785492504343953926634992332820282019728792003956564819949
#print axioms fieldPrime
local instance primeFact : Fact (Nat.Prime JHs_PDA.prime) := ⟨fieldPrime⟩
#print axioms primeFact
theorem masterY : JHs_PDA.yCoordinate (decodeState (JHj_Seeds.key)) % JHs_PDA.prime = JHt_Residues.Master.y := by
  decide +kernel
#print axioms masterY
theorem masterOffCurve : ¬ JHs_PDA.OnCurve (decodeState (JHj_Seeds.key)) := by
  unfold JHs_PDA.OnCurve
  rw [masterY]
  rintro ⟨x, _, hx⟩
  exact JHt_EulerBridge.no_solution JHs_PDA.prime
    (JHt_Residues.Master.y * JHt_Residues.Master.y + JHs_PDA.prime - 1)
    (JHs_PDA.edwardsD * JHt_Residues.Master.y * JHt_Residues.Master.y + 1)
    JHt_Residues.Master.inverse JHt_Residues.Master.ratio
    (by decide) JHt_Residues.Master.inverseCheck JHt_Residues.Master.ratioCheck
    JHt_Residues.Master.euler (by decide) ⟨x, hx⟩
#print axioms masterOffCurve
theorem checkpointY : JHs_PDA.yCoordinate (decodeState ((JHg_World.e2.snapshot 2 192 192).key)) % JHs_PDA.prime = JHt_Residues.Checkpoint.y := by
  decide +kernel
#print axioms checkpointY
theorem checkpointOffCurve : ¬ JHs_PDA.OnCurve (decodeState ((JHg_World.e2.snapshot 2 192 192).key)) := by
  unfold JHs_PDA.OnCurve
  rw [checkpointY]
  rintro ⟨x, _, hx⟩
  exact JHt_EulerBridge.no_solution JHs_PDA.prime
    (JHt_Residues.Checkpoint.y * JHt_Residues.Checkpoint.y + JHs_PDA.prime - 1)
    (JHs_PDA.edwardsD * JHt_Residues.Checkpoint.y * JHt_Residues.Checkpoint.y + 1)
    JHt_Residues.Checkpoint.inverse JHt_Residues.Checkpoint.ratio
    (by decide) JHt_Residues.Checkpoint.inverseCheck JHt_Residues.Checkpoint.ratioCheck
    JHt_Residues.Checkpoint.euler (by decide) ⟨x, hx⟩
#print axioms checkpointOffCurve
theorem laneY : JHs_PDA.yCoordinate (decodeState ((JHg_World.e2.snapshot 3 768 768).key)) % JHs_PDA.prime = JHt_Residues.Lane.y := by
  decide +kernel
#print axioms laneY
theorem laneOffCurve : ¬ JHs_PDA.OnCurve (decodeState ((JHg_World.e2.snapshot 3 768 768).key)) := by
  unfold JHs_PDA.OnCurve
  rw [laneY]
  rintro ⟨x, _, hx⟩
  exact JHt_EulerBridge.no_solution JHs_PDA.prime
    (JHt_Residues.Lane.y * JHt_Residues.Lane.y + JHs_PDA.prime - 1)
    (JHs_PDA.edwardsD * JHt_Residues.Lane.y * JHt_Residues.Lane.y + 1)
    JHt_Residues.Lane.inverse JHt_Residues.Lane.ratio
    (by decide) JHt_Residues.Lane.inverseCheck JHt_Residues.Lane.ratioCheck
    JHt_Residues.Lane.euler (by decide) ⟨x, hx⟩
#print axioms laneOffCurve
theorem registryY : JHs_PDA.yCoordinate (decodeState ((JHg_World.e2.snapshot 4 128 256).key)) % JHs_PDA.prime = JHt_Residues.Registry.y := by
  decide +kernel
#print axioms registryY
theorem registryOffCurve : ¬ JHs_PDA.OnCurve (decodeState ((JHg_World.e2.snapshot 4 128 256).key)) := by
  unfold JHs_PDA.OnCurve
  rw [registryY]
  rintro ⟨x, _, hx⟩
  exact JHt_EulerBridge.no_solution JHs_PDA.prime
    (JHt_Residues.Registry.y * JHt_Residues.Registry.y + JHs_PDA.prime - 1)
    (JHs_PDA.edwardsD * JHt_Residues.Registry.y * JHt_Residues.Registry.y + 1)
    JHt_Residues.Registry.inverse JHt_Residues.Registry.ratio
    (by decide) JHt_Residues.Registry.inverseCheck JHt_Residues.Registry.ratioCheck
    JHt_Residues.Registry.euler (by decide) ⟨x, hx⟩
#print axioms registryOffCurve
theorem registryProgramdataY : JHs_PDA.yCoordinate (decodeState (JHj_RegistryValue.registryProgramdata)) % JHs_PDA.prime = JHt_Residues.RegistryProgramdata.y := by
  decide +kernel
#print axioms registryProgramdataY
theorem registryProgramdataOffCurve : ¬ JHs_PDA.OnCurve (decodeState (JHj_RegistryValue.registryProgramdata)) := by
  unfold JHs_PDA.OnCurve
  rw [registryProgramdataY]
  rintro ⟨x, _, hx⟩
  exact JHt_EulerBridge.no_solution JHs_PDA.prime
    (JHt_Residues.RegistryProgramdata.y * JHt_Residues.RegistryProgramdata.y + JHs_PDA.prime - 1)
    (JHs_PDA.edwardsD * JHt_Residues.RegistryProgramdata.y * JHt_Residues.RegistryProgramdata.y + 1)
    JHt_Residues.RegistryProgramdata.inverse JHt_Residues.RegistryProgramdata.ratio
    (by decide) JHt_Residues.RegistryProgramdata.inverseCheck JHt_Residues.RegistryProgramdata.ratioCheck
    JHt_Residues.RegistryProgramdata.euler (by decide) ⟨x, hx⟩
#print axioms registryProgramdataOffCurve
theorem entryY : JHs_PDA.yCoordinate (decodeState ((JHg_World.e2.snapshot 5 192 320).key)) % JHs_PDA.prime = JHt_Residues.Entry.y := by
  decide +kernel
#print axioms entryY
theorem entryOffCurve : ¬ JHs_PDA.OnCurve (decodeState ((JHg_World.e2.snapshot 5 192 320).key)) := by
  unfold JHs_PDA.OnCurve
  rw [entryY]
  rintro ⟨x, _, hx⟩
  exact JHt_EulerBridge.no_solution JHs_PDA.prime
    (JHt_Residues.Entry.y * JHt_Residues.Entry.y + JHs_PDA.prime - 1)
    (JHs_PDA.edwardsD * JHt_Residues.Entry.y * JHt_Residues.Entry.y + 1)
    JHt_Residues.Entry.inverse JHt_Residues.Entry.ratio
    (by decide) JHt_Residues.Entry.inverseCheck JHt_Residues.Entry.ratioCheck
    JHt_Residues.Entry.euler (by decide) ⟨x, hx⟩
#print axioms entryOffCurve
theorem verifierProgramdataY : JHs_PDA.yCoordinate (decodeState (JHj_RegistryValue.verifierProgramdata)) % JHs_PDA.prime = JHt_Residues.VerifierProgramdata.y := by
  decide +kernel
#print axioms verifierProgramdataY
theorem verifierProgramdataOffCurve : ¬ JHs_PDA.OnCurve (decodeState (JHj_RegistryValue.verifierProgramdata)) := by
  unfold JHs_PDA.OnCurve
  rw [verifierProgramdataY]
  rintro ⟨x, _, hx⟩
  exact JHt_EulerBridge.no_solution JHs_PDA.prime
    (JHt_Residues.VerifierProgramdata.y * JHt_Residues.VerifierProgramdata.y + JHs_PDA.prime - 1)
    (JHs_PDA.edwardsD * JHt_Residues.VerifierProgramdata.y * JHt_Residues.VerifierProgramdata.y + 1)
    JHt_Residues.VerifierProgramdata.inverse JHt_Residues.VerifierProgramdata.ratio
    (by decide) JHt_Residues.VerifierProgramdata.inverseCheck JHt_Residues.VerifierProgramdata.ratioCheck
    JHt_Residues.VerifierProgramdata.euler (by decide) ⟨x, hx⟩
#print axioms verifierProgramdataOffCurve
theorem certificates : JHs_FixtureCertificates.OffCurveCertificates :=
  ⟨masterOffCurve, checkpointOffCurve, laneOffCurve, registryOffCurve,
   registryProgramdataOffCurve, entryOffCurve, verifierProgramdataOffCurve⟩
#print axioms certificates
end AspisR1.JHt_OffCurve
