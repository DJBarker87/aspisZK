import NDO_JFu_ClaimsBytes2
import NDO_JFv_MainDecode
set_option autoImplicit false
namespace AspisR1.JFu_ClaimsData
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisS1ExtractedRoundChildren

theorem decode2 : decodeMain 29#usize JFu_Q25Source.record 58#usize=ok (.Ok a2) := by
  have canonical := PSem_FieldCanonical.source_payload 25#u8 JFw_NativeRow25.record JFw_NativeRow25.payload
    (by change 14≤25;omega) JFw_NativeRow25.accepted
  have shape : JFu_Q25Source.record.framed.length=3717 := by
    simp only [JFu_Q25Source.record,JFw_NativeRow25.record,JFw_Frames.frame,Slice.length,List.length_cons]
    have size : JFw_NativeRow25.payload.val.length=3712 := JFw_NativeRow25.payload_length
    omega
  obtain ⟨out,call⟩ := JFv_MainDecode.success 29#usize JFu_Q25Source.record 58#usize
    (by change 14≤25;omega) (by rw [shape];change 5+32*(58+29)≤3717;omega)
    (by rw [shape];omega) canonical
  have cells : ∀ j : Fin 29,out.val[j.val]'(by rw [out.property];exact j.isLt)=
      a2.val[j.val]'(by rw [a2.property];exact j.isLt) := by
    intro j
    fin_cases j
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨0,by change 0<29;omega⟩ cell058 _ window058 parser058
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨1,by change 1<29;omega⟩ cell059 _ window059 parser059
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨2,by change 2<29;omega⟩ cell060 _ window060 parser060
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨3,by change 3<29;omega⟩ cell061 _ window061 parser061
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨4,by change 4<29;omega⟩ cell062 _ window062 parser062
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨5,by change 5<29;omega⟩ cell063 _ window063 parser063
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨6,by change 6<29;omega⟩ cell064 _ window064 parser064
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨7,by change 7<29;omega⟩ cell065 _ window065 parser065
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨8,by change 8<29;omega⟩ cell066 _ window066 parser066
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨9,by change 9<29;omega⟩ cell067 _ window067 parser067
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨10,by change 10<29;omega⟩ cell068 _ window068 parser068
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨11,by change 11<29;omega⟩ cell069 _ window069 parser069
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨12,by change 12<29;omega⟩ cell070 _ window070 parser070
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨13,by change 13<29;omega⟩ cell071 _ window071 parser071
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨14,by change 14<29;omega⟩ cell072 _ window072 parser072
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨15,by change 15<29;omega⟩ cell073 _ window073 parser073
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨16,by change 16<29;omega⟩ cell074 _ window074 parser074
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨17,by change 17<29;omega⟩ cell075 _ window075 parser075
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨18,by change 18<29;omega⟩ cell076 _ window076 parser076
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨19,by change 19<29;omega⟩ cell077 _ window077 parser077
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨20,by change 20<29;omega⟩ cell078 _ window078 parser078
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨21,by change 21<29;omega⟩ cell079 _ window079 parser079
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨22,by change 22<29;omega⟩ cell080 _ window080 parser080
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨23,by change 23<29;omega⟩ cell081 _ window081 parser081
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨24,by change 24<29;omega⟩ cell082 _ window082 parser082
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨25,by change 25<29;omega⟩ cell083 _ window083 parser083
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨26,by change 26<29;omega⟩ cell084 _ window084 parser084
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨27,by change 27<29;omega⟩ cell085 _ window085 parser085
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 58#usize (by change 58≤116;omega) call ⟨28,by change 28<29;omega⟩ cell086 _ window086 parser086
  have same : out=a2 := by
    apply Subtype.ext
    apply List.ext_getElem
    · rw [out.property,a2.property]
    · intro i hi hj
      exact cells ⟨i,by rw [out.property] at hi;exact hi⟩
  exact same ▸ call
#print axioms decode2
end AspisR1.JFu_ClaimsData
