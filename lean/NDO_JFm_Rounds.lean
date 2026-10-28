import NDO_JFm_RoundSteps
import NDO_JFp_InitialValue
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
  have step00 := JFm_Round00.source D hash expanded pre expand parse
  have step01 := JFm_Round01.source D hash expanded pre expand parse
  have step02 := JFm_Round02.source D hash expanded pre expand parse
  have step03 := JFm_Round03.source D hash expanded pre expand parse
  have step04 := JFm_Round04.source D hash expanded pre expand parse
  have step05 := JFm_Round05.source D hash expanded pre expand parse
  have step06 := JFm_Round06.source D hash expanded pre expand parse
  have step07 := JFm_Round07.source D hash expanded pre expand parse
  have step08 := JFm_Round08.source D hash expanded pre expand parse
  have step09 := JFm_Round09.source D hash expanded pre expand parse
  have initialDecode : children.decode 1#usize JFp_InitialValue.record 0#usize=ok (.Ok JFp_InitialValue.values) := decode
  have initialRunning : JFp_InitialValue.running=genToMain JFr_Data00.running := rfl
  have initialArray : Aeneas.Std.Array.repeat 10#usize AspisR1PublicPreparation.aspis_core.field.QM31.ZERO=JFm_PartialAlpha.a00 := rfl
  have link00 : genToMain JFr_Data00.output=genToMain JFr_Data01.running := by rfl
  have link01 : genToMain JFr_Data01.output=genToMain JFr_Data02.running := by rfl
  have link02 : genToMain JFr_Data02.output=genToMain JFr_Data03.running := by rfl
  have link03 : genToMain JFr_Data03.output=genToMain JFr_Data04.running := by rfl
  have link04 : genToMain JFr_Data04.output=genToMain JFr_Data05.running := by rfl
  have link05 : genToMain JFr_Data05.output=genToMain JFr_Data06.running := by rfl
  have link06 : genToMain JFr_Data06.output=genToMain JFr_Data07.running := by rfl
  have link07 : genToMain JFr_Data07.output=genToMain JFr_Data08.running := by rfl
  have link08 : genToMain JFr_Data08.output=genToMain JFr_Data09.running := by rfl
  dsimp only
  simp only [RoundModel.rounds,read,initialDecode,index,initialRunning,initialArray,bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,link00,link01,link02,link03,link04,link05,link06,link07,link08,step00,step01,step02,step03,step04,step05,step06,step07,step08,step09]

#print axioms source
end AspisR1.JFm_Rounds
