import NDO_JFr_Bytes02
import NDO_JFr_Round02
import NDO_JFr_BlockWindow
import NDO_JFv_MainDecode
import NDO_JFw_NativeRow17
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_Decode02
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren
open JFr_Bytes02

def record : r1_wire.ValidatedRecord := ⟨17#u8,JFw_NativeRow17.record⟩
theorem window00 : ((record.framed.val.drop 5).drop (32*0)).take 16=cell00.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 0 (by omega)]
  exact rawCell00
#print axioms window00
theorem window01 : ((record.framed.val.drop 5).drop (32*1)).take 16=cell01.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 1 (by omega)]
  exact rawCell01
#print axioms window01
theorem window02 : ((record.framed.val.drop 5).drop (32*2)).take 16=cell02.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 2 (by omega)]
  exact rawCell02
#print axioms window02
theorem window03 : ((record.framed.val.drop 5).drop (32*3)).take 16=cell03.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 3 (by omega)]
  exact rawCell03
#print axioms window03
theorem window04 : ((record.framed.val.drop 5).drop (32*4)).take 16=cell04.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 4 (by omega)]
  exact rawCell04
#print axioms window04
theorem window05 : ((record.framed.val.drop 5).drop (32*5)).take 16=cell05.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 5 (by omega)]
  exact rawCell05
#print axioms window05
theorem window06 : ((record.framed.val.drop 5).drop (32*6)).take 16=cell06.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 6 (by omega)]
  exact rawCell06
#print axioms window06
theorem window07 : ((record.framed.val.drop 5).drop (32*7)).take 16=cell07.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 7 (by omega)]
  exact rawCell07
#print axioms window07
theorem window08 : ((record.framed.val.drop 5).drop (32*8)).take 16=cell08.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 8 (by omega)]
  exact rawCell08
#print axioms window08
theorem window09 : ((record.framed.val.drop 5).drop (32*9)).take 16=cell09.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 9 (by omega)]
  exact rawCell09
#print axioms window09
theorem window10 : ((record.framed.val.drop 5).drop (32*10)).take 16=cell10.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 10 (by omega)]
  exact rawCell10
#print axioms window10
theorem window11 : ((record.framed.val.drop 5).drop (32*11)).take 16=cell11.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 11 (by omega)]
  exact rawCell11
#print axioms window11
theorem window12 : ((record.framed.val.drop 5).drop (32*12)).take 16=cell12.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 12 (by omega)]
  exact rawCell12
#print axioms window12
theorem window13 : ((record.framed.val.drop 5).drop (32*13)).take 16=cell13.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 13 (by omega)]
  exact rawCell13
#print axioms window13
theorem window14 : ((record.framed.val.drop 5).drop (32*14)).take 16=cell14.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 14 (by omega)]
  exact rawCell14
#print axioms window14
theorem window15 : ((record.framed.val.drop 5).drop (32*15)).take 16=cell15.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 15 (by omega)]
  exact rawCell15
#print axioms window15
theorem window16 : ((record.framed.val.drop 5).drop (32*16)).take 16=cell16.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 16 (by omega)]
  exact rawCell16
#print axioms window16
theorem window17 : ((record.framed.val.drop 5).drop (32*17)).take 16=cell17.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 17 (by omega)]
  exact rawCell17
#print axioms window17
theorem window18 : ((record.framed.val.drop 5).drop (32*18)).take 16=cell18.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 18 (by omega)]
  exact rawCell18
#print axioms window18
theorem window19 : ((record.framed.val.drop 5).drop (32*19)).take 16=cell19.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 19 (by omega)]
  exact rawCell19
#print axioms window19
theorem window20 : ((record.framed.val.drop 5).drop (32*20)).take 16=cell20.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 20 (by omega)]
  exact rawCell20
#print axioms window20
theorem window21 : ((record.framed.val.drop 5).drop (32*21)).take 16=cell21.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 21 (by omega)]
  exact rawCell21
#print axioms window21
theorem window22 : ((record.framed.val.drop 5).drop (32*22)).take 16=cell22.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 22 (by omega)]
  exact rawCell22
#print axioms window22
theorem window23 : ((record.framed.val.drop 5).drop (32*23)).take 16=cell23.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 23 (by omega)]
  exact rawCell23
#print axioms window23
theorem window24 : ((record.framed.val.drop 5).drop (32*24)).take 16=cell24.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 24 (by omega)]
  exact rawCell24
#print axioms window24
theorem window25 : ((record.framed.val.drop 5).drop (32*25)).take 16=cell25.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 25 (by omega)]
  exact rawCell25
#print axioms window25
theorem window26 : ((record.framed.val.drop 5).drop (32*26)).take 16=cell26.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 26 (by omega)]
  exact rawCell26
#print axioms window26
theorem window27 : ((record.framed.val.drop 5).drop (32*27)).take 16=cell27.val := by
  simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,List.drop_succ_cons,List.drop_zero]
  dsimp only [JFw_NativeRow17.payload,JFw_Frames.expandedPayload]
  dsimp only [JFw_Frames.window]
  rw [selected,JFr_BlockWindow.source 28 raw rawLength 27 (by omega)]
  exact rawCell27
#print axioms window27
theorem source : decodeMain 28#usize record 0#usize=ok (.Ok JFr_Round02.polynomial) := by
  have canonical := PSem_FieldCanonical.source_payload 17#u8 JFw_NativeRow17.record JFw_NativeRow17.payload (by change 14≤17;omega) JFw_NativeRow17.accepted
  have shape : record.framed.length=901 := by
    simp only [record,JFw_NativeRow17.record,JFw_Frames.frame,Slice.length,List.length_cons]
    have size : JFw_NativeRow17.payload.val.length=896 := JFw_NativeRow17.payload_length
    omega
  obtain ⟨out,call⟩ := JFv_MainDecode.success 28#usize record 0#usize (by change 14≤17;omega)
    (by rw [shape];change 5+32*(0+28)≤901;omega) (by rw [shape];omega) canonical
  have cells : ∀ j : Fin 28,out.val[j.val]'(by rw [out.property];exact j.isLt)=
      JFr_Round02.polynomial.val[j.val]'(by rw [JFr_Round02.polynomial.property];exact j.isLt) := by
    intro j
    fin_cases j
    · exact JFr_DecodeCell.source record out call ⟨0,by change 0<28;omega⟩ cell00 _ window00 parser00
    · exact JFr_DecodeCell.source record out call ⟨1,by change 1<28;omega⟩ cell01 _ window01 parser01
    · exact JFr_DecodeCell.source record out call ⟨2,by change 2<28;omega⟩ cell02 _ window02 parser02
    · exact JFr_DecodeCell.source record out call ⟨3,by change 3<28;omega⟩ cell03 _ window03 parser03
    · exact JFr_DecodeCell.source record out call ⟨4,by change 4<28;omega⟩ cell04 _ window04 parser04
    · exact JFr_DecodeCell.source record out call ⟨5,by change 5<28;omega⟩ cell05 _ window05 parser05
    · exact JFr_DecodeCell.source record out call ⟨6,by change 6<28;omega⟩ cell06 _ window06 parser06
    · exact JFr_DecodeCell.source record out call ⟨7,by change 7<28;omega⟩ cell07 _ window07 parser07
    · exact JFr_DecodeCell.source record out call ⟨8,by change 8<28;omega⟩ cell08 _ window08 parser08
    · exact JFr_DecodeCell.source record out call ⟨9,by change 9<28;omega⟩ cell09 _ window09 parser09
    · exact JFr_DecodeCell.source record out call ⟨10,by change 10<28;omega⟩ cell10 _ window10 parser10
    · exact JFr_DecodeCell.source record out call ⟨11,by change 11<28;omega⟩ cell11 _ window11 parser11
    · exact JFr_DecodeCell.source record out call ⟨12,by change 12<28;omega⟩ cell12 _ window12 parser12
    · exact JFr_DecodeCell.source record out call ⟨13,by change 13<28;omega⟩ cell13 _ window13 parser13
    · exact JFr_DecodeCell.source record out call ⟨14,by change 14<28;omega⟩ cell14 _ window14 parser14
    · exact JFr_DecodeCell.source record out call ⟨15,by change 15<28;omega⟩ cell15 _ window15 parser15
    · exact JFr_DecodeCell.source record out call ⟨16,by change 16<28;omega⟩ cell16 _ window16 parser16
    · exact JFr_DecodeCell.source record out call ⟨17,by change 17<28;omega⟩ cell17 _ window17 parser17
    · exact JFr_DecodeCell.source record out call ⟨18,by change 18<28;omega⟩ cell18 _ window18 parser18
    · exact JFr_DecodeCell.source record out call ⟨19,by change 19<28;omega⟩ cell19 _ window19 parser19
    · exact JFr_DecodeCell.source record out call ⟨20,by change 20<28;omega⟩ cell20 _ window20 parser20
    · exact JFr_DecodeCell.source record out call ⟨21,by change 21<28;omega⟩ cell21 _ window21 parser21
    · exact JFr_DecodeCell.source record out call ⟨22,by change 22<28;omega⟩ cell22 _ window22 parser22
    · exact JFr_DecodeCell.source record out call ⟨23,by change 23<28;omega⟩ cell23 _ window23 parser23
    · exact JFr_DecodeCell.source record out call ⟨24,by change 24<28;omega⟩ cell24 _ window24 parser24
    · exact JFr_DecodeCell.source record out call ⟨25,by change 25<28;omega⟩ cell25 _ window25 parser25
    · exact JFr_DecodeCell.source record out call ⟨26,by change 26<28;omega⟩ cell26 _ window26 parser26
    · exact JFr_DecodeCell.source record out call ⟨27,by change 27<28;omega⟩ cell27 _ window27 parser27
  have same : out=JFr_Round02.polynomial := by
    apply Subtype.ext
    apply List.ext_getElem
    · rw [out.property,JFr_Round02.polynomial.property]
    · intro i hi hj
      exact cells ⟨i,by rw [out.property] at hi;exact hi⟩
  exact same ▸ call

#print axioms source
end AspisR1.JFr_Decode02
end
