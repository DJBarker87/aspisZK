from pathlib import Path
import sys
P=Path(__file__).resolve().parent;R=P.parents[1]
s='import JFm_RoundSteps'+'''
import JFp_InitialValue
set_option autoImplicit false
namespace AspisR1.JFm_Rounds
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation AspisS1ExtractedRoundChildren
open AspisV8R19.SqueezeOracleBridge

theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    RoundModel.rounds children D0 pre
      (⟨encodeState JFm_Q14Source.ratchet,hash,15#u8⟩ : r1_wire.SemanticTranscript Hash)=
      ok (.Ok (genToMain JFr_Data09.output,JFm_PartialAlpha.a10,
        (⟨encodeState JFm_Q24Source.ratchet,hash,25#u8⟩ : r1_wire.SemanticTranscript Hash))) := by
  obtain ⟨read,decode,index⟩ := JFp_InitialValue.source expanded pre expand parse
'''
for r in range(10):s+=f'  have step{r:02} := JFm_Round{r:02}.source D hash expanded pre expand parse\n'
s+='  have initialDecode : children.decode 1#usize JFp_InitialValue.record 0#usize=ok (.Ok JFp_InitialValue.values) := decode\n  have initialRunning : JFp_InitialValue.running=genToMain JFr_Data00.running := rfl\n  have initialArray : Aeneas.Std.Array.repeat 10#usize AspisR1PublicPreparation.aspis_core.field.QM31.ZERO=JFm_PartialAlpha.a00 := rfl\n'
for r in range(9):s+=f'  have link{r:02} : genToMain JFr_Data{r:02}.output=genToMain JFr_Data{r+1:02}.running := by rfl\n'
s+='  dsimp only\n'
s+='  simp only [RoundModel.rounds,read,initialDecode,index,initialRunning,initialArray,bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,'+','.join(f'link{r:02}' for r in range(9))+','+','.join(f'step{r:02}' for r in range(10))+']\n'
s+='\n#print axioms source\nend AspisR1.JFm_Rounds\n';f=R/'lean/JFm_Rounds.lean'
if '--check' in sys.argv:assert f.read_text()==s
else:f.write_text(s)
