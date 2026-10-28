import NDO_JFu_ClaimsBytes0
import NDO_JFv_MainDecode
set_option autoImplicit false
namespace AspisR1.JFu_ClaimsData
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisS1ExtractedRoundChildren

theorem decode0 : decodeMain 29#usize JFu_Q25Source.record 0#usize=ok (.Ok a0) := by
  have canonical := PSem_FieldCanonical.source_payload 25#u8 JFw_NativeRow25.record JFw_NativeRow25.payload
    (by change 14≤25;omega) JFw_NativeRow25.accepted
  have shape : JFu_Q25Source.record.framed.length=3717 := by
    simp only [JFu_Q25Source.record,JFw_NativeRow25.record,JFw_Frames.frame,Slice.length,List.length_cons]
    have size : JFw_NativeRow25.payload.val.length=3712 := JFw_NativeRow25.payload_length
    omega
  obtain ⟨out,call⟩ := JFv_MainDecode.success 29#usize JFu_Q25Source.record 0#usize
    (by change 14≤25;omega) (by rw [shape];change 5+32*(0+29)≤3717;omega)
    (by rw [shape];omega) canonical
  have cells : ∀ j : Fin 29,out.val[j.val]'(by rw [out.property];exact j.isLt)=
      a0.val[j.val]'(by rw [a0.property];exact j.isLt) := by
    intro j
    fin_cases j
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨0,by change 0<29;omega⟩ cell000 _ window000 parser000
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨1,by change 1<29;omega⟩ cell001 _ window001 parser001
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨2,by change 2<29;omega⟩ cell002 _ window002 parser002
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨3,by change 3<29;omega⟩ cell003 _ window003 parser003
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨4,by change 4<29;omega⟩ cell004 _ window004 parser004
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨5,by change 5<29;omega⟩ cell005 _ window005 parser005
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨6,by change 6<29;omega⟩ cell006 _ window006 parser006
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨7,by change 7<29;omega⟩ cell007 _ window007 parser007
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨8,by change 8<29;omega⟩ cell008 _ window008 parser008
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨9,by change 9<29;omega⟩ cell009 _ window009 parser009
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨10,by change 10<29;omega⟩ cell010 _ window010 parser010
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨11,by change 11<29;omega⟩ cell011 _ window011 parser011
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨12,by change 12<29;omega⟩ cell012 _ window012 parser012
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨13,by change 13<29;omega⟩ cell013 _ window013 parser013
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨14,by change 14<29;omega⟩ cell014 _ window014 parser014
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨15,by change 15<29;omega⟩ cell015 _ window015 parser015
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨16,by change 16<29;omega⟩ cell016 _ window016 parser016
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨17,by change 17<29;omega⟩ cell017 _ window017 parser017
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨18,by change 18<29;omega⟩ cell018 _ window018 parser018
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨19,by change 19<29;omega⟩ cell019 _ window019 parser019
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨20,by change 20<29;omega⟩ cell020 _ window020 parser020
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨21,by change 21<29;omega⟩ cell021 _ window021 parser021
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨22,by change 22<29;omega⟩ cell022 _ window022 parser022
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨23,by change 23<29;omega⟩ cell023 _ window023 parser023
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨24,by change 24<29;omega⟩ cell024 _ window024 parser024
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨25,by change 25<29;omega⟩ cell025 _ window025 parser025
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨26,by change 26<29;omega⟩ cell026 _ window026 parser026
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨27,by change 27<29;omega⟩ cell027 _ window027 parser027
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 0#usize (by change 0≤116;omega) call ⟨28,by change 28<29;omega⟩ cell028 _ window028 parser028
  have same : out=a0 := by
    apply Subtype.ext
    apply List.ext_getElem
    · rw [out.property,a0.property]
    · intro i hi hj
      exact cells ⟨i,by rw [out.property] at hi;exact hi⟩
  exact same ▸ call
#print axioms decode0
end AspisR1.JFu_ClaimsData
