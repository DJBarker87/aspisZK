import NDO_JFm_Q14Source
import NDO_JFm_Query00Semantic
import NDO_JFm_Coordinates
import NDO_JFm_Result
import NDO_JFr_RecordsAt
set_option autoImplicit false
namespace AspisR1.JFm_Begin
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation
open AspisV8R19.SqueezeOracleBridge
def z00 : Array aspis_core.field.QM31 10#usize := Array.repeat 10#usize aspis_core.field.QM31.ZERO
def z01 : Array aspis_core.field.QM31 10#usize := ⟨[JFm_Coordinates.value03,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO],by rfl⟩
def z02 : Array aspis_core.field.QM31 10#usize := ⟨[JFm_Coordinates.value03,JFm_Coordinates.value04,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO],by rfl⟩
def z03 : Array aspis_core.field.QM31 10#usize := ⟨[JFm_Coordinates.value03,JFm_Coordinates.value04,JFm_Coordinates.value05,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO],by rfl⟩
def z04 : Array aspis_core.field.QM31 10#usize := ⟨[JFm_Coordinates.value03,JFm_Coordinates.value04,JFm_Coordinates.value05,JFm_Coordinates.value06,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO],by rfl⟩
def z05 : Array aspis_core.field.QM31 10#usize := ⟨[JFm_Coordinates.value03,JFm_Coordinates.value04,JFm_Coordinates.value05,JFm_Coordinates.value06,JFm_Coordinates.value07,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO],by rfl⟩
def z06 : Array aspis_core.field.QM31 10#usize := ⟨[JFm_Coordinates.value03,JFm_Coordinates.value04,JFm_Coordinates.value05,JFm_Coordinates.value06,JFm_Coordinates.value07,JFm_Coordinates.value08,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO],by rfl⟩
def z07 : Array aspis_core.field.QM31 10#usize := ⟨[JFm_Coordinates.value03,JFm_Coordinates.value04,JFm_Coordinates.value05,JFm_Coordinates.value06,JFm_Coordinates.value07,JFm_Coordinates.value08,JFm_Coordinates.value09,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO],by rfl⟩
def z08 : Array aspis_core.field.QM31 10#usize := ⟨[JFm_Coordinates.value03,JFm_Coordinates.value04,JFm_Coordinates.value05,JFm_Coordinates.value06,JFm_Coordinates.value07,JFm_Coordinates.value08,JFm_Coordinates.value09,JFm_Coordinates.value10,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO],by rfl⟩
def z09 : Array aspis_core.field.QM31 10#usize := ⟨[JFm_Coordinates.value03,JFm_Coordinates.value04,JFm_Coordinates.value05,JFm_Coordinates.value06,JFm_Coordinates.value07,JFm_Coordinates.value08,JFm_Coordinates.value09,JFm_Coordinates.value10,JFm_Coordinates.value11,aspis_core.field.QM31.ZERO],by rfl⟩
def z10 : Array aspis_core.field.QM31 10#usize := ⟨[JFm_Coordinates.value03,JFm_Coordinates.value04,JFm_Coordinates.value05,JFm_Coordinates.value06,JFm_Coordinates.value07,JFm_Coordinates.value08,JFm_Coordinates.value09,JFm_Coordinates.value10,JFm_Coordinates.value11,JFm_Coordinates.value12],by rfl⟩
theorem index00 : Array.index_mut_usize z00 0#usize=ok (aspis_core.field.QM31.ZERO,Aeneas.Std.Array.set z00 0#usize) := by rfl
#print axioms index00
theorem update00 : Aeneas.Std.Array.set z00 0#usize JFm_Coordinates.value03=z01 := by rfl
#print axioms update00
theorem index01 : Array.index_mut_usize z01 1#usize=ok (aspis_core.field.QM31.ZERO,Aeneas.Std.Array.set z01 1#usize) := by rfl
#print axioms index01
theorem update01 : Aeneas.Std.Array.set z01 1#usize JFm_Coordinates.value04=z02 := by rfl
#print axioms update01
theorem index02 : Array.index_mut_usize z02 2#usize=ok (aspis_core.field.QM31.ZERO,Aeneas.Std.Array.set z02 2#usize) := by rfl
#print axioms index02
theorem update02 : Aeneas.Std.Array.set z02 2#usize JFm_Coordinates.value05=z03 := by rfl
#print axioms update02
theorem index03 : Array.index_mut_usize z03 3#usize=ok (aspis_core.field.QM31.ZERO,Aeneas.Std.Array.set z03 3#usize) := by rfl
#print axioms index03
theorem update03 : Aeneas.Std.Array.set z03 3#usize JFm_Coordinates.value06=z04 := by rfl
#print axioms update03
theorem index04 : Array.index_mut_usize z04 4#usize=ok (aspis_core.field.QM31.ZERO,Aeneas.Std.Array.set z04 4#usize) := by rfl
#print axioms index04
theorem update04 : Aeneas.Std.Array.set z04 4#usize JFm_Coordinates.value07=z05 := by rfl
#print axioms update04
theorem index05 : Array.index_mut_usize z05 5#usize=ok (aspis_core.field.QM31.ZERO,Aeneas.Std.Array.set z05 5#usize) := by rfl
#print axioms index05
theorem update05 : Aeneas.Std.Array.set z05 5#usize JFm_Coordinates.value08=z06 := by rfl
#print axioms update05
theorem index06 : Array.index_mut_usize z06 6#usize=ok (aspis_core.field.QM31.ZERO,Aeneas.Std.Array.set z06 6#usize) := by rfl
#print axioms index06
theorem update06 : Aeneas.Std.Array.set z06 6#usize JFm_Coordinates.value09=z07 := by rfl
#print axioms update06
theorem index07 : Array.index_mut_usize z07 7#usize=ok (aspis_core.field.QM31.ZERO,Aeneas.Std.Array.set z07 7#usize) := by rfl
#print axioms index07
theorem update07 : Aeneas.Std.Array.set z07 7#usize JFm_Coordinates.value10=z08 := by rfl
#print axioms update07
theorem index08 : Array.index_mut_usize z08 8#usize=ok (aspis_core.field.QM31.ZERO,Aeneas.Std.Array.set z08 8#usize) := by rfl
#print axioms index08
theorem update08 : Aeneas.Std.Array.set z08 8#usize JFm_Coordinates.value11=z09 := by rfl
#print axioms update08
theorem index09 : Array.index_mut_usize z09 9#usize=ok (aspis_core.field.QM31.ZERO,Aeneas.Std.Array.set z09 9#usize) := by rfl
#print axioms index09
theorem update09 : Aeneas.Std.Array.set z09 9#usize JFm_Coordinates.value12=z10 := by rfl
#print axioms update09
def challenges : r1_wire.Challenges := ⟨JFm_Coordinates.value00,JFm_Coordinates.value01,JFm_Coordinates.value02,z10,JFm_Coordinates.value13,JFm_Coordinates.value14⟩
theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    r1_wire.begin D0 pre
      (⟨encodeState JFr_SeedBoundary.numeric,hash,0#u8⟩ : r1_wire.SemanticTranscript Hash)=
      ok (.Ok challenges,(⟨encodeState JFm_Q14Source.ratchet,hash,15#u8⟩ : r1_wire.SemanticTranscript Hash)) := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
  obtain ⟨q00,call00,coords00⟩ := JFm_Query00Semantic.source D hash
  have same00 : q00=JFm_Coordinates.value00 := JFm_Coordinates.injective coords00
  rw [same00] at call00
  dsimp only [JFm_Query00Semantic.record] at call00
  have read00 := JFr_RecordsAt.source pre records 0#u8 (by change 0<27;omega) JFw_NativeRow00.record rfl
  obtain ⟨q01,call01,coords01⟩ := JFm_Q01Source.semantic D hash
  have same01 : q01=JFm_Coordinates.value01 := JFm_Coordinates.injective coords01
  rw [same01] at call01
  dsimp only [JFm_Q01Source.record] at call01
  have read01 := JFr_RecordsAt.source pre records 1#u8 (by change 1<27;omega) JFw_NativeRow01.record rfl
  obtain ⟨q02,call02,coords02⟩ := JFm_Q02Source.semantic D hash
  have same02 : q02=JFm_Coordinates.value02 := JFm_Coordinates.injective coords02
  rw [same02] at call02
  dsimp only [JFm_Q02Source.record] at call02
  have read02 := JFr_RecordsAt.source pre records 2#u8 (by change 2<27;omega) JFw_NativeRow02.record rfl
  obtain ⟨q03,call03,coords03⟩ := JFm_Q03Source.semantic D hash
  have same03 : q03=JFm_Coordinates.value03 := JFm_Coordinates.injective coords03
  rw [same03] at call03
  dsimp only [JFm_Q03Source.record] at call03
  have read03 := JFr_RecordsAt.source pre records 3#u8 (by change 3<27;omega) JFw_NativeRow03.record rfl
  obtain ⟨q04,call04,coords04⟩ := JFm_Q04Source.semantic D hash
  have same04 : q04=JFm_Coordinates.value04 := JFm_Coordinates.injective coords04
  rw [same04] at call04
  dsimp only [JFm_Q04Source.record] at call04
  have read04 := JFr_RecordsAt.source pre records 4#u8 (by change 4<27;omega) JFw_NativeRow04.record rfl
  obtain ⟨q05,call05,coords05⟩ := JFm_Q05Source.semantic D hash
  have same05 : q05=JFm_Coordinates.value05 := JFm_Coordinates.injective coords05
  rw [same05] at call05
  dsimp only [JFm_Q05Source.record] at call05
  have read05 := JFr_RecordsAt.source pre records 5#u8 (by change 5<27;omega) JFw_NativeRow05.record rfl
  obtain ⟨q06,call06,coords06⟩ := JFm_Q06Source.semantic D hash
  have same06 : q06=JFm_Coordinates.value06 := JFm_Coordinates.injective coords06
  rw [same06] at call06
  dsimp only [JFm_Q06Source.record] at call06
  have read06 := JFr_RecordsAt.source pre records 6#u8 (by change 6<27;omega) JFw_NativeRow06.record rfl
  obtain ⟨q07,call07,coords07⟩ := JFm_Q07Source.semantic D hash
  have same07 : q07=JFm_Coordinates.value07 := JFm_Coordinates.injective coords07
  rw [same07] at call07
  dsimp only [JFm_Q07Source.record] at call07
  have read07 := JFr_RecordsAt.source pre records 7#u8 (by change 7<27;omega) JFw_NativeRow07.record rfl
  obtain ⟨q08,call08,coords08⟩ := JFm_Q08Source.semantic D hash
  have same08 : q08=JFm_Coordinates.value08 := JFm_Coordinates.injective coords08
  rw [same08] at call08
  dsimp only [JFm_Q08Source.record] at call08
  have read08 := JFr_RecordsAt.source pre records 8#u8 (by change 8<27;omega) JFw_NativeRow08.record rfl
  obtain ⟨q09,call09,coords09⟩ := JFm_Q09Source.semantic D hash
  have same09 : q09=JFm_Coordinates.value09 := JFm_Coordinates.injective coords09
  rw [same09] at call09
  dsimp only [JFm_Q09Source.record] at call09
  have read09 := JFr_RecordsAt.source pre records 9#u8 (by change 9<27;omega) JFw_NativeRow09.record rfl
  obtain ⟨q10,call10,coords10⟩ := JFm_Q10Source.semantic D hash
  have same10 : q10=JFm_Coordinates.value10 := JFm_Coordinates.injective coords10
  rw [same10] at call10
  dsimp only [JFm_Q10Source.record] at call10
  have read10 := JFr_RecordsAt.source pre records 10#u8 (by change 10<27;omega) JFw_NativeRow10.record rfl
  obtain ⟨q11,call11,coords11⟩ := JFm_Q11Source.semantic D hash
  have same11 : q11=JFm_Coordinates.value11 := JFm_Coordinates.injective coords11
  rw [same11] at call11
  dsimp only [JFm_Q11Source.record] at call11
  have read11 := JFr_RecordsAt.source pre records 11#u8 (by change 11<27;omega) JFw_NativeRow11.record rfl
  obtain ⟨q12,call12,coords12⟩ := JFm_Q12Source.semantic D hash
  have same12 : q12=JFm_Coordinates.value12 := JFm_Coordinates.injective coords12
  rw [same12] at call12
  dsimp only [JFm_Q12Source.record] at call12
  have read12 := JFr_RecordsAt.source pre records 12#u8 (by change 12<27;omega) JFw_NativeRow12.record rfl
  obtain ⟨q13,call13,coords13⟩ := JFm_Q13Source.semantic D hash
  have same13 : q13=JFm_Coordinates.value13 := JFm_Coordinates.injective coords13
  rw [same13] at call13
  dsimp only [JFm_Q13Source.record] at call13
  have read13 := JFr_RecordsAt.source pre records 13#u8 (by change 13<27;omega) JFw_NativeRow13.record rfl
  obtain ⟨q14,call14,coords14⟩ := JFm_Q14Source.semantic D hash
  have same14 : q14=JFm_Coordinates.value14 := JFm_Coordinates.injective coords14
  rw [same14] at call14
  dsimp only [JFm_Q14Source.record] at call14
  have read14 := JFr_RecordsAt.source pre records 14#u8 (by change 14<27;omega) JFw_NativeRow14.record rfl
  have initial_array : Array.repeat 10#usize aspis_core.field.QM31.ZERO=z00 := rfl
  dsimp only
  unfold r1_wire.begin
  simp (config := {zeta := true,zetaDelta := true}) only [bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,read00,call00,read01,call01,read02,call02,read03,call03,read04,call04,read05,call05,read06,call06,read07,call07,read08,call08,read09,call09,read10,call10,read11,call11,read12,call12,read13,call13,read14,call14,initial_array,index00,update00,index01,update01,index02,update02,index03,update03,index04,update04,index05,update05,index06,update06,index07,update07,index08,update08,index09,update09,JFm_Result.pair_ok]
  rfl
#print axioms source
end AspisR1.JFm_Begin
