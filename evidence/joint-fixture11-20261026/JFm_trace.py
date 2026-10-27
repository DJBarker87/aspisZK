from pathlib import Path
import sys
P=Path(__file__).resolve().parent;R=P.parents[1]
ns='JFm_RealTrace';v=lambda i:f'JFm_Coordinates.value{i:02}'
rows='['+','.join(f'{i}#u8' for i in range(25))+']';vals='['+','.join(v(i) for i in range(25))+']'
s='''import JFm_Q24Source
import JFm_Query00Semantic
import JFm_Coordinates
import JFr_RecordsAt
set_option autoImplicit false
namespace AspisR1.JFm_RealTrace
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation
open AspisV8R19.SqueezeOracleBridge
'''
s+=f'def rows : List U8 := {rows}\ndef values : List aspis_core.field.QM31 := {vals}\n'
s+='''theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    BeginCalls.SemanticRun D0 pre rows
      (⟨encodeState JFr_SeedBoundary.numeric,hash,0#u8⟩ : r1_wire.SemanticTranscript Hash)
      (⟨encodeState JFm_Q24Source.ratchet,hash,25#u8⟩ : r1_wire.SemanticTranscript Hash) values := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
'''
for i in range(25):
 src='JFm_Query00Semantic.source' if i==0 else f'JFm_Q{i:02}Source.semantic'
 s+=f'  obtain ⟨q{i:02},call{i:02},coords{i:02}⟩ := {src} D hash\n'
 s+=f'  have same{i:02} : q{i:02}={v(i)} := JFm_Coordinates.injective coords{i:02}\n'
 s+=f'  rw [same{i:02}] at call{i:02}\n'
 s+=f'  have read{i:02} := JFr_RecordsAt.source pre records {i}#u8 (by change {i}<27;omega) JFw_NativeRow{i:02}.record rfl\n'
s+='  dsimp only\n  unfold rows values\n'
for i in range(25):s+=f'  refine .cons read{i:02} call{i:02} ?_\n'
s+='  exact .nil _\n#print axioms source\n'
s+='''theorem frames {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ cs : List (SourceFull25.Call D0 pre),
      SourceFull25.Trace D0 pre
        (⟨encodeState JFr_SeedBoundary.numeric,hash,0#u8⟩ : r1_wire.SemanticTranscript Hash)
        (⟨encodeState JFm_Q24Source.ratchet,hash,25#u8⟩ : r1_wire.SemanticTranscript Hash) cs ∧
      cs.map SourceFull25.Call.row=rows ∧ cs.map SourceFull25.Call.q=values ∧
      cs.map (fun c => c.record.framed)=pre.records.val.take 25 := by
  exact SourceFull25.run_full25_frames _ pre (source D hash expanded pre expand parse) rfl
#print axioms frames
end AspisR1.JFm_RealTrace
'''
f=R/'lean/JFm_RealTrace.lean'
if '--check' in sys.argv:assert f.read_text()==s
else:f.write_text(s)
