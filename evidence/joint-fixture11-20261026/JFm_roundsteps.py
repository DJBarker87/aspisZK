from pathlib import Path
import sys
P=Path(__file__).resolve().parent;R=P.parents[1];files={}
for r in range(10):
 i=r+15;mod=f'JFm_Round{r:02}'
 module=f'JFm_Q{i:02}Source'
 s=f'''import {module}
import JFm_PartialAlpha
import JFm_Result
import JFr_RecordsAt
set_option autoImplicit false
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation AspisS1ExtractedRoundChildren
open AspisV8R19.SqueezeOracleBridge

theorem comparison : core.cmp.PartialEq.ne.trait_default
    AspisR1PublicPreparation.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
    (genToMain JFr_Data{r:02}.running) (genToMain JFr_Data{r:02}.running)=ok false := by rfl
#print axioms comparison

theorem source {{Hash : Type}} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    RoundModel.step children D0 pre
      (⟨encodeState JFm_Q{i-1:02}Source.ratchet,hash,{i}#u8⟩ : r1_wire.SemanticTranscript Hash)
      JFm_PartialAlpha.a{r:02} (genToMain JFr_Data{r:02}.running) {r}#usize=
      ok (.Ok (genToMain JFr_Data{r:02}.output,JFm_PartialAlpha.a{r+1:02},
        (⟨encodeState JFm_Q{i:02}Source.ratchet,hash,{i+1}#u8⟩ : r1_wire.SemanticTranscript Hash))) := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
  have read := JFr_RecordsAt.source pre records {i}#u8 (by change {i}<27;omega) JFw_NativeRow{i:02}.record rfl
  obtain ⟨vr,old,decode⟩ := JFr_RealRounds.decoded expanded pre expand parse ⟨{r},by omega⟩
  have sameRecord : vr=(⟨{i}#u8,JFw_NativeRow{i:02}.record⟩ : r1_wire.ValidatedRecord) :=
    core.result.Result.Ok.inj (Result.ok.inj (old.symm.trans read))
  rw [sameRecord] at decode
  change decodeMain 28#usize ⟨{i}#u8,JFw_NativeRow{i:02}.record⟩ 0#usize=ok (.Ok JFr_Round{r:02}.polynomial) at decode
  obtain ⟨q,call,coords⟩ := JFm_Q{i:02}Source.semantic D hash
  have same : q=JFm_Coordinates.value{i:02} := JFm_Coordinates.injective coords
  rw [same] at call
  dsimp only [JFm_Q{i:02}Source.record] at call
  have add : 15#u8 + UScalar.cast .U8 {r}#usize=ok {i}#u8 := by
    obtain ⟨v,success,value⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := 15#u8) (y := UScalar.cast .U8 {r}#usize) (by scalar_tac))
    have sameV : v={i}#u8 := by scalar_tac
    exact sameV ▸ success
  dsimp only
  simp only [RoundModel.step,children,generatedRoundBoundaries,lift,bind_tc_ok,add,read,
    Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,decode,JFr_Round{r:02}.boundary,comparison,
    Bool.false_eq_true,if_false,call,JFm_Result.pair_ok,JFm_PartialAlpha.update{r:02},JFm_PartialAlpha.value{r:02}]

#print axioms source
end AspisR1.{mod}
'''
 files[R/'lean'/(mod+'.lean')]=s
imports=list(dict.fromkeys(line for text in files.values() for line in text.splitlines() if line.startswith('import ')))
body='\n'.join('\n'.join(line for line in text.splitlines() if not line.startswith('import ')) for text in files.values())
files={R/'lean/JFm_RoundSteps.lean':'\n'.join(imports)+'\n'+body+'\n'}
for f,s in files.items():
 if '--check' in sys.argv:assert f.read_text()==s
 else:f.write_text(s)
