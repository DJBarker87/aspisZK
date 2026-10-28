import NDO_JHs_FixtureCertificates
import JHt_Prime
import JHt_EulerBridge
import JHt_Residues
set_option autoImplicit false
namespace AspisR1.JHt_OffCurve
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JHt_BinaryModPow.modPow
theorem fieldPrime : Nat.Prime JHs_PDA.prime := JHt_Prime.prime_57896044618658097711785492504343953926634992332820282019728792003956564819949
#print axioms fieldPrime
local instance primeFact : Fact (Nat.Prime JHs_PDA.prime) := ⟨fieldPrime⟩
#print axioms primeFact
theorem ofY (h : AspisV8R19.SourceDuplexStep.State) (y vi r : Nat)
    (hy : JHs_PDA.yCoordinate h % JHs_PDA.prime = y)
    (hi : (JHs_PDA.edwardsD * y*y + 1) * vi % JHs_PDA.prime = 1)
    (hr : (y*y + JHs_PDA.prime - 1) * vi % JHs_PDA.prime = r)
    (he : JHt_BinaryModPow.modPow r (JHs_PDA.prime / 2) JHs_PDA.prime 256 = JHs_PDA.prime - 1) :
    ¬ JHs_PDA.OnCurve h := by
  rintro ⟨x, _, hx⟩
  change ((JHs_PDA.edwardsD * (JHs_PDA.yCoordinate h % JHs_PDA.prime) *
    (JHs_PDA.yCoordinate h % JHs_PDA.prime) + 1) * x*x) % JHs_PDA.prime =
    ((JHs_PDA.yCoordinate h % JHs_PDA.prime) * (JHs_PDA.yCoordinate h % JHs_PDA.prime) + JHs_PDA.prime - 1) % JHs_PDA.prime at hx
  rw [hy] at hx
  exact JHt_EulerBridge.no_solution JHs_PDA.prime
    (y*y + JHs_PDA.prime - 1) (JHs_PDA.edwardsD * y*y + 1) vi r
    (by decide) hi hr he (by decide) ⟨x, hx⟩
#print axioms ofY

theorem masterY : JHs_PDA.yCoordinate (decodeState (JHj_Seeds.key)) % JHs_PDA.prime = JHt_Residues.Master.y := by
  decide +kernel
#print axioms masterY
theorem masterOffCurve : ¬ JHs_PDA.OnCurve (decodeState (JHj_Seeds.key)) := by
  exact ofY _ _ _ _ masterY JHt_Residues.Master.inverseCheck
    JHt_Residues.Master.ratioCheck JHt_Residues.Master.euler
#print axioms masterOffCurve
theorem checkpointY : JHs_PDA.yCoordinate (decodeState ((JHg_World.e2.snapshot 2 192 192).key)) % JHs_PDA.prime = JHt_Residues.Checkpoint.y := by
  decide +kernel
#print axioms checkpointY
theorem checkpointOffCurve : ¬ JHs_PDA.OnCurve (decodeState ((JHg_World.e2.snapshot 2 192 192).key)) := by
  exact ofY _ _ _ _ checkpointY JHt_Residues.Checkpoint.inverseCheck
    JHt_Residues.Checkpoint.ratioCheck JHt_Residues.Checkpoint.euler
#print axioms checkpointOffCurve
theorem laneY : JHs_PDA.yCoordinate (decodeState ((JHg_World.e2.snapshot 3 768 768).key)) % JHs_PDA.prime = JHt_Residues.Lane.y := by
  decide +kernel
#print axioms laneY
theorem laneOffCurve : ¬ JHs_PDA.OnCurve (decodeState ((JHg_World.e2.snapshot 3 768 768).key)) := by
  exact ofY _ _ _ _ laneY JHt_Residues.Lane.inverseCheck
    JHt_Residues.Lane.ratioCheck JHt_Residues.Lane.euler
#print axioms laneOffCurve
theorem registryY : JHs_PDA.yCoordinate (decodeState ((JHg_World.e2.snapshot 4 128 256).key)) % JHs_PDA.prime = JHt_Residues.Registry.y := by
  decide +kernel
#print axioms registryY
theorem registryOffCurve : ¬ JHs_PDA.OnCurve (decodeState ((JHg_World.e2.snapshot 4 128 256).key)) := by
  exact ofY _ _ _ _ registryY JHt_Residues.Registry.inverseCheck
    JHt_Residues.Registry.ratioCheck JHt_Residues.Registry.euler
#print axioms registryOffCurve
theorem registryProgramdataY : JHs_PDA.yCoordinate (decodeState (JHj_RegistryValue.registryProgramdata)) % JHs_PDA.prime = JHt_Residues.RegistryProgramdata.y := by
  decide +kernel
#print axioms registryProgramdataY
theorem registryProgramdataOffCurve : ¬ JHs_PDA.OnCurve (decodeState (JHj_RegistryValue.registryProgramdata)) := by
  exact ofY _ _ _ _ registryProgramdataY JHt_Residues.RegistryProgramdata.inverseCheck
    JHt_Residues.RegistryProgramdata.ratioCheck JHt_Residues.RegistryProgramdata.euler
#print axioms registryProgramdataOffCurve
theorem entryY : JHs_PDA.yCoordinate (decodeState ((JHg_World.e2.snapshot 5 192 320).key)) % JHs_PDA.prime = JHt_Residues.Entry.y := by
  decide +kernel
#print axioms entryY
theorem entryOffCurve : ¬ JHs_PDA.OnCurve (decodeState ((JHg_World.e2.snapshot 5 192 320).key)) := by
  exact ofY _ _ _ _ entryY JHt_Residues.Entry.inverseCheck
    JHt_Residues.Entry.ratioCheck JHt_Residues.Entry.euler
#print axioms entryOffCurve
theorem verifierProgramdataY : JHs_PDA.yCoordinate (decodeState (JHj_RegistryValue.verifierProgramdata)) % JHs_PDA.prime = JHt_Residues.VerifierProgramdata.y := by
  decide +kernel
#print axioms verifierProgramdataY
theorem verifierProgramdataOffCurve : ¬ JHs_PDA.OnCurve (decodeState (JHj_RegistryValue.verifierProgramdata)) := by
  exact ofY _ _ _ _ verifierProgramdataY JHt_Residues.VerifierProgramdata.inverseCheck
    JHt_Residues.VerifierProgramdata.ratioCheck JHt_Residues.VerifierProgramdata.euler
#print axioms verifierProgramdataOffCurve
theorem certificates : JHs_FixtureCertificates.OffCurveCertificates :=
  ⟨masterOffCurve, checkpointOffCurve, laneOffCurve, registryOffCurve,
   registryProgramdataOffCurve, entryOffCurve, verifierProgramdataOffCurve⟩
#print axioms certificates
end AspisR1.JHt_OffCurve
