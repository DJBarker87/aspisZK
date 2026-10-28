import NDO_JFu_ClaimsBytes1
import NDO_JFv_MainDecode
set_option autoImplicit false
namespace AspisR1.JFu_ClaimsData
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisS1ExtractedRoundChildren

theorem decode1 : decodeMain 29#usize JFu_Q25Source.record 29#usize=ok (.Ok a1) := by
  have canonical := PSem_FieldCanonical.source_payload 25#u8 JFw_NativeRow25.record JFw_NativeRow25.payload
    (by change 14≤25;omega) JFw_NativeRow25.accepted
  have shape : JFu_Q25Source.record.framed.length=3717 := by
    simp only [JFu_Q25Source.record,JFw_NativeRow25.record,JFw_Frames.frame,Slice.length,List.length_cons]
    have size : JFw_NativeRow25.payload.val.length=3712 := JFw_NativeRow25.payload_length
    omega
  obtain ⟨out,call⟩ := JFv_MainDecode.success 29#usize JFu_Q25Source.record 29#usize
    (by change 14≤25;omega) (by rw [shape];change 5+32*(29+29)≤3717;omega)
    (by rw [shape];omega) canonical
  have cells : ∀ j : Fin 29,out.val[j.val]'(by rw [out.property];exact j.isLt)=
      a1.val[j.val]'(by rw [a1.property];exact j.isLt) := by
    intro j
    fin_cases j
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨0,by change 0<29;omega⟩ cell029 _ window029 parser029
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨1,by change 1<29;omega⟩ cell030 _ window030 parser030
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨2,by change 2<29;omega⟩ cell031 _ window031 parser031
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨3,by change 3<29;omega⟩ cell032 _ window032 parser032
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨4,by change 4<29;omega⟩ cell033 _ window033 parser033
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨5,by change 5<29;omega⟩ cell034 _ window034 parser034
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨6,by change 6<29;omega⟩ cell035 _ window035 parser035
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨7,by change 7<29;omega⟩ cell036 _ window036 parser036
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨8,by change 8<29;omega⟩ cell037 _ window037 parser037
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨9,by change 9<29;omega⟩ cell038 _ window038 parser038
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨10,by change 10<29;omega⟩ cell039 _ window039 parser039
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨11,by change 11<29;omega⟩ cell040 _ window040 parser040
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨12,by change 12<29;omega⟩ cell041 _ window041 parser041
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨13,by change 13<29;omega⟩ cell042 _ window042 parser042
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨14,by change 14<29;omega⟩ cell043 _ window043 parser043
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨15,by change 15<29;omega⟩ cell044 _ window044 parser044
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨16,by change 16<29;omega⟩ cell045 _ window045 parser045
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨17,by change 17<29;omega⟩ cell046 _ window046 parser046
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨18,by change 18<29;omega⟩ cell047 _ window047 parser047
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨19,by change 19<29;omega⟩ cell048 _ window048 parser048
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨20,by change 20<29;omega⟩ cell049 _ window049 parser049
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨21,by change 21<29;omega⟩ cell050 _ window050 parser050
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨22,by change 22<29;omega⟩ cell051 _ window051 parser051
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨23,by change 23<29;omega⟩ cell052 _ window052 parser052
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨24,by change 24<29;omega⟩ cell053 _ window053 parser053
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨25,by change 25<29;omega⟩ cell054 _ window054 parser054
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨26,by change 26<29;omega⟩ cell055 _ window055 parser055
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨27,by change 27<29;omega⟩ cell056 _ window056 parser056
    · exact JFu_DecodeAt.source JFu_Q25Source.record out 29#usize (by change 29≤116;omega) call ⟨28,by change 28<29;omega⟩ cell057 _ window057 parser057
  have same : out=a1 := by
    apply Subtype.ext
    apply List.ext_getElem
    · rw [out.property,a1.property]
    · intro i hi hj
      exact cells ⟨i,by rw [out.property] at hi;exact hi⟩
  exact same ▸ call
#print axioms decode1
end AspisR1.JFu_ClaimsData
