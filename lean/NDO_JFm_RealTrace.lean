import NDO_JFm_Q24Source
import NDO_JFm_Query00Semantic
import NDO_JFm_Coordinates
import NDO_JFr_RecordsAt
set_option autoImplicit false
namespace AspisR1.JFm_RealTrace
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation
open AspisV8R19.SqueezeOracleBridge
def rows : List U8 := [0#u8,1#u8,2#u8,3#u8,4#u8,5#u8,6#u8,7#u8,8#u8,9#u8,10#u8,11#u8,12#u8,13#u8,14#u8,15#u8,16#u8,17#u8,18#u8,19#u8,20#u8,21#u8,22#u8,23#u8,24#u8]
def values : List aspis_core.field.QM31 := [JFm_Coordinates.value00,JFm_Coordinates.value01,JFm_Coordinates.value02,JFm_Coordinates.value03,JFm_Coordinates.value04,JFm_Coordinates.value05,JFm_Coordinates.value06,JFm_Coordinates.value07,JFm_Coordinates.value08,JFm_Coordinates.value09,JFm_Coordinates.value10,JFm_Coordinates.value11,JFm_Coordinates.value12,JFm_Coordinates.value13,JFm_Coordinates.value14,JFm_Coordinates.value15,JFm_Coordinates.value16,JFm_Coordinates.value17,JFm_Coordinates.value18,JFm_Coordinates.value19,JFm_Coordinates.value20,JFm_Coordinates.value21,JFm_Coordinates.value22,JFm_Coordinates.value23,JFm_Coordinates.value24]
theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    BeginCalls.SemanticRun D0 pre rows
      (⟨encodeState JFr_SeedBoundary.numeric,hash,0#u8⟩ : r1_wire.SemanticTranscript Hash)
      (⟨encodeState JFm_Q24Source.ratchet,hash,25#u8⟩ : r1_wire.SemanticTranscript Hash) values := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
  obtain ⟨q00,call00,coords00⟩ := JFm_Query00Semantic.source D hash
  have same00 : q00=JFm_Coordinates.value00 := JFm_Coordinates.injective coords00
  rw [same00] at call00
  have read00 := JFr_RecordsAt.source pre records 0#u8 (by change 0<27;omega) JFw_NativeRow00.record rfl
  obtain ⟨q01,call01,coords01⟩ := JFm_Q01Source.semantic D hash
  have same01 : q01=JFm_Coordinates.value01 := JFm_Coordinates.injective coords01
  rw [same01] at call01
  have read01 := JFr_RecordsAt.source pre records 1#u8 (by change 1<27;omega) JFw_NativeRow01.record rfl
  obtain ⟨q02,call02,coords02⟩ := JFm_Q02Source.semantic D hash
  have same02 : q02=JFm_Coordinates.value02 := JFm_Coordinates.injective coords02
  rw [same02] at call02
  have read02 := JFr_RecordsAt.source pre records 2#u8 (by change 2<27;omega) JFw_NativeRow02.record rfl
  obtain ⟨q03,call03,coords03⟩ := JFm_Q03Source.semantic D hash
  have same03 : q03=JFm_Coordinates.value03 := JFm_Coordinates.injective coords03
  rw [same03] at call03
  have read03 := JFr_RecordsAt.source pre records 3#u8 (by change 3<27;omega) JFw_NativeRow03.record rfl
  obtain ⟨q04,call04,coords04⟩ := JFm_Q04Source.semantic D hash
  have same04 : q04=JFm_Coordinates.value04 := JFm_Coordinates.injective coords04
  rw [same04] at call04
  have read04 := JFr_RecordsAt.source pre records 4#u8 (by change 4<27;omega) JFw_NativeRow04.record rfl
  obtain ⟨q05,call05,coords05⟩ := JFm_Q05Source.semantic D hash
  have same05 : q05=JFm_Coordinates.value05 := JFm_Coordinates.injective coords05
  rw [same05] at call05
  have read05 := JFr_RecordsAt.source pre records 5#u8 (by change 5<27;omega) JFw_NativeRow05.record rfl
  obtain ⟨q06,call06,coords06⟩ := JFm_Q06Source.semantic D hash
  have same06 : q06=JFm_Coordinates.value06 := JFm_Coordinates.injective coords06
  rw [same06] at call06
  have read06 := JFr_RecordsAt.source pre records 6#u8 (by change 6<27;omega) JFw_NativeRow06.record rfl
  obtain ⟨q07,call07,coords07⟩ := JFm_Q07Source.semantic D hash
  have same07 : q07=JFm_Coordinates.value07 := JFm_Coordinates.injective coords07
  rw [same07] at call07
  have read07 := JFr_RecordsAt.source pre records 7#u8 (by change 7<27;omega) JFw_NativeRow07.record rfl
  obtain ⟨q08,call08,coords08⟩ := JFm_Q08Source.semantic D hash
  have same08 : q08=JFm_Coordinates.value08 := JFm_Coordinates.injective coords08
  rw [same08] at call08
  have read08 := JFr_RecordsAt.source pre records 8#u8 (by change 8<27;omega) JFw_NativeRow08.record rfl
  obtain ⟨q09,call09,coords09⟩ := JFm_Q09Source.semantic D hash
  have same09 : q09=JFm_Coordinates.value09 := JFm_Coordinates.injective coords09
  rw [same09] at call09
  have read09 := JFr_RecordsAt.source pre records 9#u8 (by change 9<27;omega) JFw_NativeRow09.record rfl
  obtain ⟨q10,call10,coords10⟩ := JFm_Q10Source.semantic D hash
  have same10 : q10=JFm_Coordinates.value10 := JFm_Coordinates.injective coords10
  rw [same10] at call10
  have read10 := JFr_RecordsAt.source pre records 10#u8 (by change 10<27;omega) JFw_NativeRow10.record rfl
  obtain ⟨q11,call11,coords11⟩ := JFm_Q11Source.semantic D hash
  have same11 : q11=JFm_Coordinates.value11 := JFm_Coordinates.injective coords11
  rw [same11] at call11
  have read11 := JFr_RecordsAt.source pre records 11#u8 (by change 11<27;omega) JFw_NativeRow11.record rfl
  obtain ⟨q12,call12,coords12⟩ := JFm_Q12Source.semantic D hash
  have same12 : q12=JFm_Coordinates.value12 := JFm_Coordinates.injective coords12
  rw [same12] at call12
  have read12 := JFr_RecordsAt.source pre records 12#u8 (by change 12<27;omega) JFw_NativeRow12.record rfl
  obtain ⟨q13,call13,coords13⟩ := JFm_Q13Source.semantic D hash
  have same13 : q13=JFm_Coordinates.value13 := JFm_Coordinates.injective coords13
  rw [same13] at call13
  have read13 := JFr_RecordsAt.source pre records 13#u8 (by change 13<27;omega) JFw_NativeRow13.record rfl
  obtain ⟨q14,call14,coords14⟩ := JFm_Q14Source.semantic D hash
  have same14 : q14=JFm_Coordinates.value14 := JFm_Coordinates.injective coords14
  rw [same14] at call14
  have read14 := JFr_RecordsAt.source pre records 14#u8 (by change 14<27;omega) JFw_NativeRow14.record rfl
  obtain ⟨q15,call15,coords15⟩ := JFm_Q15Source.semantic D hash
  have same15 : q15=JFm_Coordinates.value15 := JFm_Coordinates.injective coords15
  rw [same15] at call15
  have read15 := JFr_RecordsAt.source pre records 15#u8 (by change 15<27;omega) JFw_NativeRow15.record rfl
  obtain ⟨q16,call16,coords16⟩ := JFm_Q16Source.semantic D hash
  have same16 : q16=JFm_Coordinates.value16 := JFm_Coordinates.injective coords16
  rw [same16] at call16
  have read16 := JFr_RecordsAt.source pre records 16#u8 (by change 16<27;omega) JFw_NativeRow16.record rfl
  obtain ⟨q17,call17,coords17⟩ := JFm_Q17Source.semantic D hash
  have same17 : q17=JFm_Coordinates.value17 := JFm_Coordinates.injective coords17
  rw [same17] at call17
  have read17 := JFr_RecordsAt.source pre records 17#u8 (by change 17<27;omega) JFw_NativeRow17.record rfl
  obtain ⟨q18,call18,coords18⟩ := JFm_Q18Source.semantic D hash
  have same18 : q18=JFm_Coordinates.value18 := JFm_Coordinates.injective coords18
  rw [same18] at call18
  have read18 := JFr_RecordsAt.source pre records 18#u8 (by change 18<27;omega) JFw_NativeRow18.record rfl
  obtain ⟨q19,call19,coords19⟩ := JFm_Q19Source.semantic D hash
  have same19 : q19=JFm_Coordinates.value19 := JFm_Coordinates.injective coords19
  rw [same19] at call19
  have read19 := JFr_RecordsAt.source pre records 19#u8 (by change 19<27;omega) JFw_NativeRow19.record rfl
  obtain ⟨q20,call20,coords20⟩ := JFm_Q20Source.semantic D hash
  have same20 : q20=JFm_Coordinates.value20 := JFm_Coordinates.injective coords20
  rw [same20] at call20
  have read20 := JFr_RecordsAt.source pre records 20#u8 (by change 20<27;omega) JFw_NativeRow20.record rfl
  obtain ⟨q21,call21,coords21⟩ := JFm_Q21Source.semantic D hash
  have same21 : q21=JFm_Coordinates.value21 := JFm_Coordinates.injective coords21
  rw [same21] at call21
  have read21 := JFr_RecordsAt.source pre records 21#u8 (by change 21<27;omega) JFw_NativeRow21.record rfl
  obtain ⟨q22,call22,coords22⟩ := JFm_Q22Source.semantic D hash
  have same22 : q22=JFm_Coordinates.value22 := JFm_Coordinates.injective coords22
  rw [same22] at call22
  have read22 := JFr_RecordsAt.source pre records 22#u8 (by change 22<27;omega) JFw_NativeRow22.record rfl
  obtain ⟨q23,call23,coords23⟩ := JFm_Q23Source.semantic D hash
  have same23 : q23=JFm_Coordinates.value23 := JFm_Coordinates.injective coords23
  rw [same23] at call23
  have read23 := JFr_RecordsAt.source pre records 23#u8 (by change 23<27;omega) JFw_NativeRow23.record rfl
  obtain ⟨q24,call24,coords24⟩ := JFm_Q24Source.semantic D hash
  have same24 : q24=JFm_Coordinates.value24 := JFm_Coordinates.injective coords24
  rw [same24] at call24
  have read24 := JFr_RecordsAt.source pre records 24#u8 (by change 24<27;omega) JFw_NativeRow24.record rfl
  dsimp only
  unfold rows values
  refine .cons read00 call00 ?_
  refine .cons read01 call01 ?_
  refine .cons read02 call02 ?_
  refine .cons read03 call03 ?_
  refine .cons read04 call04 ?_
  refine .cons read05 call05 ?_
  refine .cons read06 call06 ?_
  refine .cons read07 call07 ?_
  refine .cons read08 call08 ?_
  refine .cons read09 call09 ?_
  refine .cons read10 call10 ?_
  refine .cons read11 call11 ?_
  refine .cons read12 call12 ?_
  refine .cons read13 call13 ?_
  refine .cons read14 call14 ?_
  refine .cons read15 call15 ?_
  refine .cons read16 call16 ?_
  refine .cons read17 call17 ?_
  refine .cons read18 call18 ?_
  refine .cons read19 call19 ?_
  refine .cons read20 call20 ?_
  refine .cons read21 call21 ?_
  refine .cons read22 call22 ?_
  refine .cons read23 call23 ?_
  refine .cons read24 call24 ?_
  exact .nil _
#print axioms source
theorem frames {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
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
