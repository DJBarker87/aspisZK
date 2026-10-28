import NDO_JFu_ClaimsBytes3
import NDO_JFv_MainDecode
set_option autoImplicit false
namespace AspisR1.JFu_ClaimsData
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisS1ExtractedRoundChildren

theorem decode3 : decodeMain 29#usize JFu_Q25Source.record 87#usize=ok (.Ok a3) := by
  have canonical := PSem_FieldCanonical.source_payload 25#u8 JFw_NativeRow25.record JFw_NativeRow25.payload
    (by change 14≤25;omega) JFw_NativeRow25.accepted
  have shape : JFu_Q25Source.record.framed.length=3717 := by
    simp only [JFu_Q25Source.record,JFw_NativeRow25.record,JFw_Frames.frame,Slice.length,List.length_cons]
    have size : JFw_NativeRow25.payload.val.length=3712 := JFw_NativeRow25.payload_length
    omega
  obtain ⟨out,call⟩ := JFv_MainDecode.success 29#usize JFu_Q25Source.record 87#usize
    (by change 14≤25;omega) (by rw [shape];change 5+32*(87+29)≤3717;omega)
    (by rw [shape];omega) canonical
  have cells : ∀ j : Fin 29,out.val[j.val]'(by rw [out.property];exact j.isLt)=
      a3.val[j.val]'(by rw [a3.property];exact j.isLt) := by
    intro j
    fin_cases j
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨0,by change 0<29;omega⟩ cell087 _ window087 parser087
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨1,by change 1<29;omega⟩ cell088 _ window088 parser088
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨2,by change 2<29;omega⟩ cell089 _ window089 parser089
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨3,by change 3<29;omega⟩ cell090 _ window090 parser090
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨4,by change 4<29;omega⟩ cell091 _ window091 parser091
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨5,by change 5<29;omega⟩ cell092 _ window092 parser092
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨6,by change 6<29;omega⟩ cell093 _ window093 parser093
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨7,by change 7<29;omega⟩ cell094 _ window094 parser094
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨8,by change 8<29;omega⟩ cell095 _ window095 parser095
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨9,by change 9<29;omega⟩ cell096 _ window096 parser096
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨10,by change 10<29;omega⟩ cell097 _ window097 parser097
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨11,by change 11<29;omega⟩ cell098 _ window098 parser098
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨12,by change 12<29;omega⟩ cell099 _ window099 parser099
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨13,by change 13<29;omega⟩ cell100 _ window100 parser100
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨14,by change 14<29;omega⟩ cell101 _ window101 parser101
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨15,by change 15<29;omega⟩ cell102 _ window102 parser102
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨16,by change 16<29;omega⟩ cell103 _ window103 parser103
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨17,by change 17<29;omega⟩ cell104 _ window104 parser104
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨18,by change 18<29;omega⟩ cell105 _ window105 parser105
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨19,by change 19<29;omega⟩ cell106 _ window106 parser106
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨20,by change 20<29;omega⟩ cell107 _ window107 parser107
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨21,by change 21<29;omega⟩ cell108 _ window108 parser108
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨22,by change 22<29;omega⟩ cell109 _ window109 parser109
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨23,by change 23<29;omega⟩ cell110 _ window110 parser110
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨24,by change 24<29;omega⟩ cell111 _ window111 parser111
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨25,by change 25<29;omega⟩ cell112 _ window112 parser112
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨26,by change 26<29;omega⟩ cell113 _ window113 parser113
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨27,by change 27<29;omega⟩ cell114 _ window114 parser114
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 87#usize (by change 87≤116;omega) call ⟨28,by change 28<29;omega⟩ cell115 _ window115 parser115
  have same : out=a3 := by
    apply Subtype.ext
    apply List.ext_getElem
    · rw [out.property,a3.property]
    · intro i hi hj
      exact cells ⟨i,by rw [out.property] at hi;exact hi⟩
  exact same ▸ call
#print axioms decode3
end AspisR1.JFu_ClaimsData
