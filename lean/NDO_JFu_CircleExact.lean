import NDO_JFu_CircleParameters
import NDO_JFu_CirclePair
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_CircleExact
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.SamplerCirclePolicy

def z0 := JFu_CircleAlgebra.nativePoint (point JFu_CircleParameters.t25)
def z1 := JFu_CircleAlgebra.nativePoint (point JFu_CircleParameters.t26)
theorem value25 : F3M_CircleSource.source (encodeState JFu_Q25Source.block) .First=ok z0 :=
  JFu_CircleAlgebra.source _ _ JFu_CircleParameters.q25 JFu_CircleParameters.sample25
    JFu_CircleParameters.canon25 JFu_CircleParameters.outside25
#print axioms value25
theorem canonical25 : SAP_CanonicalCarrier.CanonK z0.x ∧ SAP_CanonicalCarrier.CanonK z0.y :=
  SAP_CircleCanonical.source _ _ _ value25
#print axioms canonical25
theorem circle25 {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (B : FinishModel.Boundaries) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    FinishModel.circle_validated (F3M_CircleSource.install B) D0
      (⟨encodeState JFm_Q24Source.ratchet,hash,25#u8⟩ : r1_wire.SemanticTranscript Hash)
      JFu_Q25Source.record=ok (.Ok z0,
        (⟨encodeState JFu_Q25Source.ratchet,hash,26#u8⟩ : r1_wire.SemanticTranscript Hash)) := by
  try dsimp only
  simp only [FinishModel.circle_validated,r1_wire.ValidatedRecord.impl.row,
    r1_wire.ValidatedRecord.impl.framed,JFu_Q25Source.record,bind_tc_ok]
  rw [JFu_Q25Source.source,bind_tc_ok]
  change (do let p ← F3M_CircleSource.source (encodeState JFu_Q25Source.block) .First
             ok ((core.result.Result.Ok p : core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error),
               (⟨encodeState JFu_Q25Source.ratchet,hash,26#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [value25,bind_tc_ok]
#print axioms circle25
theorem value26 : F3M_CircleSource.source (encodeState JFu_Q26Source.block) .Second=ok z1 :=
  JFu_CircleAlgebra.source _ _ JFu_CircleParameters.q26 JFu_CircleParameters.sample26
    JFu_CircleParameters.canon26 JFu_CircleParameters.outside26
#print axioms value26
theorem canonical26 : SAP_CanonicalCarrier.CanonK z1.x ∧ SAP_CanonicalCarrier.CanonK z1.y :=
  SAP_CircleCanonical.source _ _ _ value26
#print axioms canonical26
theorem circle26 {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (B : FinishModel.Boundaries) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    FinishModel.circle_validated (F3M_CircleSource.install B) D0
      (⟨encodeState JFu_Q25Source.ratchet,hash,26#u8⟩ : r1_wire.SemanticTranscript Hash)
      JFu_Q26Source.record=ok (.Ok z1,
        (⟨encodeState JFu_Q26Source.ratchet,hash,27#u8⟩ : r1_wire.SemanticTranscript Hash)) := by
  try dsimp only
  simp only [FinishModel.circle_validated,r1_wire.ValidatedRecord.impl.row,
    r1_wire.ValidatedRecord.impl.framed,JFu_Q26Source.record,bind_tc_ok]
  rw [JFu_Q26Source.source,bind_tc_ok]
  change (do let p ← F3M_CircleSource.source (encodeState JFu_Q26Source.block) .Second
             ok ((core.result.Result.Ok p : core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error),
               (⟨encodeState JFu_Q26Source.ratchet,hash,27#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [value26,bind_tc_ok]
#print axioms circle26
theorem different : z0 ≠ z1 :=
  JFu_CircleAlgebra.distinct _ _ JFu_CircleParameters.outside25 JFu_CircleParameters.outside26
    JFu_CircleParameters.different

theorem inequality : FinishModel.pointEq z0 z1=ok false :=
  JFu_CircleAlgebra.comparison _ _ different

#print axioms different
#print axioms inequality
end AspisR1.JFu_CircleExact
end
