from pathlib import Path
import sys
P=Path(__file__).resolve().parent;R=P.parents[1];v=lambda i:f'JFm_Coordinates.value{i:02}'
s='''import JFm_Q14Source
import JFm_Query00Semantic
import JFm_Coordinates
import JFm_Result
import JFr_RecordsAt
set_option autoImplicit false
namespace AspisR1.JFm_Begin
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation
open AspisV8R19.SqueezeOracleBridge
'''
zero='aspis_core.field.QM31.ZERO'
arr=lambda n:'⟨['+','.join(v(i+3) if i<n else zero for i in range(10))+'],by rfl⟩'
s+='def z00 : Array aspis_core.field.QM31 10#usize := Array.repeat 10#usize aspis_core.field.QM31.ZERO\n'
for i in range(1,11):s+=f'def z{i:02} : Array aspis_core.field.QM31 10#usize := {arr(i)}\n'
for i in range(10):
 s+=f'theorem index{i:02} : Array.index_mut_usize z{i:02} {i}#usize=ok ({zero},Aeneas.Std.Array.set z{i:02} {i}#usize) := by rfl\n#print axioms index{i:02}\n'
 s+=f'theorem update{i:02} : Aeneas.Std.Array.set z{i:02} {i}#usize {v(i+3)}=z{i+1:02} := by rfl\n#print axioms update{i:02}\n'
s+=f'def challenges : r1_wire.Challenges := ⟨{v(0)},{v(1)},{v(2)},z10,{v(13)},{v(14)}⟩\n'
s+='''theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    r1_wire.begin D0 pre
      (⟨encodeState JFr_SeedBoundary.numeric,hash,0#u8⟩ : r1_wire.SemanticTranscript Hash)=
      ok (.Ok challenges,(⟨encodeState JFm_Q14Source.ratchet,hash,15#u8⟩ : r1_wire.SemanticTranscript Hash)) := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
'''
for i in range(15):
 src='JFm_Query00Semantic.source' if i==0 else f'JFm_Q{i:02}Source.semantic'
 s+=f'  obtain ⟨q{i:02},call{i:02},coords{i:02}⟩ := {src} D hash\n'
 s+=f'  have same{i:02} : q{i:02}={v(i)} := JFm_Coordinates.injective coords{i:02}\n'
 s+=f'  rw [same{i:02}] at call{i:02}\n'
 rec='JFm_Query00Semantic.record' if i==0 else f'JFm_Q{i:02}Source.record'
 s+=f'  dsimp only [{rec}] at call{i:02}\n'
 s+=f'  have read{i:02} := JFr_RecordsAt.source pre records {i}#u8 (by change {i}<27;omega) JFw_NativeRow{i:02}.record rfl\n'
s+='  have initial_array : Array.repeat 10#usize aspis_core.field.QM31.ZERO=z00 := rfl\n  dsimp only\n  unfold r1_wire.begin\n'
s+='  simp (config := {zeta := true,zetaDelta := true}) only [bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,'+','.join(f'read{i:02},call{i:02}' for i in range(15))+',initial_array,'+','.join(f'index{i:02},update{i:02}' for i in range(10))+',JFm_Result.pair_ok]\n'
s+='  rfl\n#print axioms source\nend AspisR1.JFm_Begin\n'
f=R/'lean/JFm_Begin.lean'
if '--check' in sys.argv:assert f.read_text()==s
else:f.write_text(s)
