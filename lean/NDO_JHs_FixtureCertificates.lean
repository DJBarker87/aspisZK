import NDO_JHs_Inputs
set_option autoImplicit false
namespace AspisR1.JHs_FixtureCertificates
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open AspisV8R19.SqueezeOracleBridge
/-- Exactly one mathematical SHA equation for each reached PDA call. -/
structure SHARealization : Prop where
  masterDigestEquation : JFp_SHADigest.digest (JHs_PDA.preimage JHj_Seeds.master JHb_Programs.pool) = decodeState JHj_Seeds.key
  checkpointDigestEquation : JFp_SHADigest.digest (JHs_PDA.preimage JHj_Seeds.checkpoint JHb_Programs.pool) = decodeState (JHg_World.e2.snapshot 2 192 192).key
  laneDigestEquation : JFp_SHADigest.digest (JHs_PDA.preimage JHj_Seeds.lane JHb_Programs.pool) = decodeState (JHg_World.e2.snapshot 3 768 768).key
  registryDigestEquation : JFp_SHADigest.digest (JHs_PDA.preimage JHj_RegistrySeeds.registry JHb_Programs.registry) = decodeState (JHg_World.e2.snapshot 4 128 256).key
  registryProgramdataDigestEquation : JFp_SHADigest.digest (JHs_PDA.preimage JHj_RegistrySeeds.registryProgramdata JHj_RegistryValue.loader) = decodeState JHj_RegistryValue.registryProgramdata
  entryDigestEquation : JFp_SHADigest.digest (JHs_PDA.preimage JHj_RegistrySeeds.entry JHb_Programs.registry) = decodeState (JHg_World.e2.snapshot 5 192 320).key
  verifierProgramdataDigestEquation : JFp_SHADigest.digest (JHs_PDA.preimage JHj_RegistrySeeds.verifierProgramdata JHj_RegistryValue.loader) = decodeState JHj_RegistryValue.verifierProgramdata

/-- Concrete off-curve propositions only; no successful callback or caller observation. -/
structure OffCurveCertificates : Prop where
  masterOffCurve : JHs_PDA.OffCurve (decodeState JHj_Seeds.key)
  checkpointOffCurve : JHs_PDA.OffCurve (decodeState (JHg_World.e2.snapshot 2 192 192).key)
  laneOffCurve : JHs_PDA.OffCurve (decodeState (JHg_World.e2.snapshot 3 768 768).key)
  registryOffCurve : JHs_PDA.OffCurve (decodeState (JHg_World.e2.snapshot 4 128 256).key)
  registryProgramdataOffCurve : JHs_PDA.OffCurve (decodeState JHj_RegistryValue.registryProgramdata)
  entryOffCurve : JHs_PDA.OffCurve (decodeState (JHg_World.e2.snapshot 5 192 320).key)
  verifierProgramdataOffCurve : JHs_PDA.OffCurve (decodeState JHj_RegistryValue.verifierProgramdata)

theorem master (sha : SHARealization) (curve : OffCurveCertificates) :
    JHs_PDA.derive JHj_Seeds.master JHb_Programs.pool = ok (.Ok JHj_Seeds.key) :=
  JHs_PDA.certified _ _ _ JHs_Inputs.Master.valid sha.masterDigestEquation curve.masterOffCurve
#print axioms master

theorem checkpoint (sha : SHARealization) (curve : OffCurveCertificates) :
    JHs_PDA.derive JHj_Seeds.checkpoint JHb_Programs.pool = ok (.Ok (JHg_World.e2.snapshot 2 192 192).key) :=
  JHs_PDA.certified _ _ _ JHs_Inputs.Checkpoint.valid sha.checkpointDigestEquation curve.checkpointOffCurve
#print axioms checkpoint

theorem lane (sha : SHARealization) (curve : OffCurveCertificates) :
    JHs_PDA.derive JHj_Seeds.lane JHb_Programs.pool = ok (.Ok (JHg_World.e2.snapshot 3 768 768).key) :=
  JHs_PDA.certified _ _ _ JHs_Inputs.Lane.valid sha.laneDigestEquation curve.laneOffCurve
#print axioms lane

theorem registry (sha : SHARealization) (curve : OffCurveCertificates) :
    JHs_PDA.derive JHj_RegistrySeeds.registry JHb_Programs.registry = ok (.Ok (JHg_World.e2.snapshot 4 128 256).key) :=
  JHs_PDA.certified _ _ _ JHs_Inputs.Registry.valid sha.registryDigestEquation curve.registryOffCurve
#print axioms registry

theorem registryProgramdata (sha : SHARealization) (curve : OffCurveCertificates) :
    JHs_PDA.derive JHj_RegistrySeeds.registryProgramdata JHj_RegistryValue.loader = ok (.Ok JHj_RegistryValue.registryProgramdata) :=
  JHs_PDA.certified _ _ _ JHs_Inputs.RegistryProgramdata.valid sha.registryProgramdataDigestEquation curve.registryProgramdataOffCurve
#print axioms registryProgramdata

theorem entry (sha : SHARealization) (curve : OffCurveCertificates) :
    JHs_PDA.derive JHj_RegistrySeeds.entry JHb_Programs.registry = ok (.Ok (JHg_World.e2.snapshot 5 192 320).key) :=
  JHs_PDA.certified _ _ _ JHs_Inputs.Entry.valid sha.entryDigestEquation curve.entryOffCurve
#print axioms entry

theorem verifierProgramdata (sha : SHARealization) (curve : OffCurveCertificates) :
    JHs_PDA.derive JHj_RegistrySeeds.verifierProgramdata JHj_RegistryValue.loader = ok (.Ok JHj_RegistryValue.verifierProgramdata) :=
  JHs_PDA.certified _ _ _ JHs_Inputs.VerifierProgramdata.valid sha.verifierProgramdataDigestEquation curve.verifierProgramdataOffCurve
#print axioms verifierProgramdata
end AspisR1.JHs_FixtureCertificates
