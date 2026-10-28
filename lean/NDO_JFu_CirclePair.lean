import NDO_JFu_Q25Source
import NDO_JFu_Q26Source
import NDO_JFm_ChallengeFixture
import NDO_JFv_CircleTotal
import NDO_JFr_RecordsAt
import NDO_JFr_PrefixRecords
set_option autoImplicit false
namespace AspisR1.JFu_CirclePair
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation
open AspisV8R19.SqueezeOracleBridge
theorem circle25 {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (B : FinishModel.Boundaries) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ p,FinishModel.circle_validated (F3M_CircleSource.install B) D0
      (⟨encodeState JFm_Q24Source.ratchet,hash,25#u8⟩ : r1_wire.SemanticTranscript Hash)
      JFu_Q25Source.record=ok (.Ok p,
        (⟨encodeState JFu_Q25Source.ratchet,hash,26#u8⟩ : r1_wire.SemanticTranscript Hash)) ∧
      SAP_CanonicalCarrier.CanonK p.x ∧ SAP_CanonicalCarrier.CanonK p.y := by
  obtain ⟨p,call,canon⟩ := JFv_CircleTotal.source (encodeState JFu_Q25Source.block) .First
  refine ⟨p,?_,canon⟩
  try dsimp only
  simp only [FinishModel.circle_validated,r1_wire.ValidatedRecord.impl.row,
    r1_wire.ValidatedRecord.impl.framed,JFu_Q25Source.record,bind_tc_ok]
  rw [JFu_Q25Source.source,bind_tc_ok]
  change (do let p ← F3M_CircleSource.source (encodeState JFu_Q25Source.block) .First
             ok ((core.result.Result.Ok p : core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error),
               (⟨encodeState JFu_Q25Source.ratchet,hash,26#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [call,bind_tc_ok]
#print axioms circle25
theorem circle26 {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (B : FinishModel.Boundaries) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ p,FinishModel.circle_validated (F3M_CircleSource.install B) D0
      (⟨encodeState JFu_Q25Source.ratchet,hash,26#u8⟩ : r1_wire.SemanticTranscript Hash)
      JFu_Q26Source.record=ok (.Ok p,
        (⟨encodeState JFu_Q26Source.ratchet,hash,27#u8⟩ : r1_wire.SemanticTranscript Hash)) ∧
      SAP_CanonicalCarrier.CanonK p.x ∧ SAP_CanonicalCarrier.CanonK p.y := by
  obtain ⟨p,call,canon⟩ := JFv_CircleTotal.source (encodeState JFu_Q26Source.block) .Second
  refine ⟨p,?_,canon⟩
  try dsimp only
  simp only [FinishModel.circle_validated,r1_wire.ValidatedRecord.impl.row,
    r1_wire.ValidatedRecord.impl.framed,JFu_Q26Source.record,bind_tc_ok]
  rw [JFu_Q26Source.source,bind_tc_ok]
  change (do let p ← F3M_CircleSource.source (encodeState JFu_Q26Source.block) .Second
             ok ((core.result.Result.Ok p : core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error),
               (⟨encodeState JFu_Q26Source.ratchet,hash,27#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [call,bind_tc_ok]
#print axioms circle26
theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (B : FinishModel.Boundaries) (hash : Hash) (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ z0 z1,
    r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok JFu_Q25Source.record) ∧
    r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok JFu_Q26Source.record) ∧
    FinishModel.circle_validated (F3M_CircleSource.install B) D0
      (⟨encodeState JFm_Q24Source.ratchet,hash,25#u8⟩ : r1_wire.SemanticTranscript Hash) JFu_Q25Source.record=
      ok (.Ok z0,(⟨encodeState JFu_Q25Source.ratchet,hash,26#u8⟩ : r1_wire.SemanticTranscript Hash)) ∧
    FinishModel.circle_validated (F3M_CircleSource.install B) D0
      (⟨encodeState JFu_Q25Source.ratchet,hash,26#u8⟩ : r1_wire.SemanticTranscript Hash) JFu_Q26Source.record=
      ok (.Ok z1,(⟨encodeState JFu_Q26Source.ratchet,hash,27#u8⟩ : r1_wire.SemanticTranscript Hash)) ∧
    (SAP_CanonicalCarrier.CanonK z0.x ∧ SAP_CanonicalCarrier.CanonK z0.y) ∧
    (SAP_CanonicalCarrier.CanonK z1.x ∧ SAP_CanonicalCarrier.CanonK z1.y) := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
  have read25 := JFr_RecordsAt.source pre records 25#u8 (by change 25<27;omega) JFw_NativeRow25.record rfl
  have read26 := JFr_RecordsAt.source pre records 26#u8 (by change 26<27;omega) JFw_NativeRow26.record rfl
  obtain ⟨z0,call0,canon0⟩ := circle25 D B hash
  obtain ⟨z1,call1,canon1⟩ := circle26 D B hash
  exact ⟨z0,z1,read25,read26,call0,call1,canon0,canon1⟩
#print axioms source
end AspisR1.JFu_CirclePair
