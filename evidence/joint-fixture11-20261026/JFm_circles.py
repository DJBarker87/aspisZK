from pathlib import Path
import sys
P=Path(__file__).resolve().parent;R=P.parents[1]
def read_part(i):
 f=R/f'lean/JFm_Q{i:02}Source.lean'
 if not f.exists():f=P/'JFm_UNCHECKED'/(f.name+'.txt')
 return f.read_text()
texts=[read_part(i) for i in [25,26]]
imports=list(dict.fromkeys(l for t in texts for l in t.splitlines() if l.startswith('import ') and l!='import JFm_Q25Source'))
imports+=['import Rc10_Top','import JFm_ChallengeFixture','import JFv_CircleTotal']
s='\n'.join(imports)+'\n'+'\n'.join(l for t in texts for l in t.splitlines() if not l.startswith('import '))+'\n'
s+='''namespace AspisR1.JFm_CirclePair
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation
open AspisV8R19.SqueezeOracleBridge
'''
for i,row in [(25,'First'),(26,'Second')]:
 s+=f'''theorem circle{i} {{Hash : Type}} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (B : FinishModel.Boundaries) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ p,FinishModel.circle_validated (F3M_CircleSource.install B) D0
      (⟨encodeState JFm_Q{i-1:02}Source.ratchet,hash,{i}#u8⟩ : r1_wire.SemanticTranscript Hash)
      JFm_Q{i:02}Source.record=ok (.Ok p,
        (⟨encodeState JFm_Q{i:02}Source.ratchet,hash,{i+1}#u8⟩ : r1_wire.SemanticTranscript Hash)) ∧
      SAP_CanonicalCarrier.CanonK p.x ∧ SAP_CanonicalCarrier.CanonK p.y := by
  obtain ⟨p,call,canon⟩ := JFv_CircleTotal.source (encodeState JFm_Q{i:02}Source.block) .{row}
  refine ⟨p,?_,canon⟩
  dsimp only
  simp only [FinishModel.circle_validated,r1_wire.ValidatedRecord.impl.row,
    r1_wire.ValidatedRecord.impl.framed,JFm_Q{i:02}Source.record,bind_tc_ok]
  rw [JFm_Q{i:02}Source.source,bind_tc_ok]
  change (do let p ← F3M_CircleSource.source (encodeState JFm_Q{i:02}Source.block) .{row}
             ok ((core.result.Result.Ok p : core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error),
               (⟨encodeState JFm_Q{i:02}Source.ratchet,hash,{i+1}#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [call,bind_tc_ok]
#print axioms circle{i}
'''
s+='''theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (B : FinishModel.Boundaries) (hash : Hash) (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ z0 z1,
    r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok JFm_Q25Source.record) ∧
    r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok JFm_Q26Source.record) ∧
    FinishModel.circle_validated (F3M_CircleSource.install B) D0
      (⟨encodeState JFm_Q24Source.ratchet,hash,25#u8⟩ : r1_wire.SemanticTranscript Hash) JFm_Q25Source.record=
      ok (.Ok z0,(⟨encodeState JFm_Q25Source.ratchet,hash,26#u8⟩ : r1_wire.SemanticTranscript Hash)) ∧
    FinishModel.circle_validated (F3M_CircleSource.install B) D0
      (⟨encodeState JFm_Q25Source.ratchet,hash,26#u8⟩ : r1_wire.SemanticTranscript Hash) JFm_Q26Source.record=
      ok (.Ok z1,(⟨encodeState JFm_Q26Source.ratchet,hash,27#u8⟩ : r1_wire.SemanticTranscript Hash)) ∧
    (SAP_CanonicalCarrier.CanonK z0.x ∧ SAP_CanonicalCarrier.CanonK z0.y) ∧
    (SAP_CanonicalCarrier.CanonK z1.x ∧ SAP_CanonicalCarrier.CanonK z1.y) := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
  have read25 := JFr_RecordsAt.source pre records 25#u8 (by change 25<27;omega) JFw_NativeRow25.record rfl
  have read26 := JFr_RecordsAt.source pre records 26#u8 (by change 26<27;omega) JFw_NativeRow26.record rfl
  obtain ⟨z0,call0,canon0⟩ := circle25 D B hash
  obtain ⟨z1,call1,canon1⟩ := circle26 D B hash
  exact ⟨z0,z1,read25,read26,call0,call1,canon0,canon1⟩
#print axioms source
end AspisR1.JFm_CirclePair
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#print AspisR1.Rc10_Top.deployed
#print axioms AspisR1.Rc10_Top.deployed
#print AspisR1.JFm_ChallengeFixture.inhabited
#print axioms AspisR1.JFm_ChallengeFixture.inhabited
#print axioms AspisR1.JFm_RealTrace.frames
#print axioms AspisR1.JFm_Rounds.source
#print axioms AspisR1.JFm_Begin.source
'''
f=R/'lean/JFm_CirclePair.lean'
if '--check' in sys.argv:
 checked=f if f.exists() else P/'JFm_UNCHECKED'/(f.name+'.txt')
 assert checked.read_text()==s
else:f.write_text(s)
