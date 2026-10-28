import PV_B3P_FrontierOutcome226V3
import PV_B3P_NativeFieldByte226V3
import PV_B3P_LayoutCells226V3
namespace PV_B3P_FrontierValue226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_ByteLayout226V3
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
theorem complete_result (a : Array (Array U32 8#usize) 20#usize)
    (i : Usize) (hi : i.val < 640) :
    PV_B3P_FrontierOutcome226V3.frontierAt a i =
      if (frontier a)[i.val / 4]?.getD 0#u32 < 2147483647#u32 then
        .ok (.Ok ((fields (frontier a))[i.val]?.getD 0#u8))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  obtain ⟨q,hq,hqval⟩ := UScalar.div_spec (x:=i) (y:=32#usize) (by decide)
  obtain ⟨r,hr,hrval⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (x:=i) (y:=32#usize) (by decide))
  obtain ⟨s,hs,hsval⟩ := UScalar.div_spec (x:=r) (y:=4#usize) (by decide)
  obtain ⟨t,ht,htval⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (x:=i) (y:=4#usize) (by decide))
  have hqnat : q.val = i.val / 32 := by simpa using hqval
  have hrnat : r.val = i.val % 32 := by simpa using hrval
  have hsnat : s.val = r.val / 4 := by simpa using hsval
  have htnat : t.val = i.val % 4 := by simpa using htval
  have hqb : q.val < (20#usize).val := by
    have hn : (20#usize).val = 20 := rfl
    rw [hn,hqnat]; omega
  have hsb : s.val < (8#usize).val := by
    have hn : (8#usize).val = 8 := rfl
    rw [hn,hsnat,hrnat]; omega
  have hql : q.val < a.val.length := by simpa [a.property] using hqb
  let row := a.val[q.val]'hql
  have hsl : s.val < row.val.length := by simpa [row.property] using hsb
  have htb : t.val < 4 := by rw [htnat]; omega
  have hwordIndex : 8*q.val+s.val = i.val/4 := by
    rw [hqnat,hsnat,hrnat]; omega
  have hflat : 8*q.val+s.val < (frontier a).length := by
    rw [frontier_length,hwordIndex]; omega
  have hword : (frontier a)[8*q.val+s.val]'hflat = row.val[s.val]'hsl := by
    have hc := PV_B3P_LayoutCells226V3.frontier_cell a q.val s.val hql hsb
    rw [List.getElem?_eq_getElem hflat,List.getElem?_eq_getElem hsl] at hc
    exact Option.some.inj hc
  have hsel : (frontier a)[i.val/4]?.getD 0#u32 = row.val[s.val]'hsl := by
    rw [← hwordIndex,List.getElem?_eq_getElem hflat,hword]
    rfl
  have hidx : 4*(8*q.val+s.val)+t.val = i.val := by
    rw [hwordIndex,htnat]; omega
  have hwl : t.val < (wordBytes (row.val[s.val]'hsl)).length := by
    simpa only [wordBytes,List.length_cons,List.length_nil] using htb
  have hc := PV_B3P_LayoutCells226V3.fields_cell (frontier a)
    (8*q.val+s.val) t.val hflat htb
  rw [hidx,hword,List.getElem?_eq_getElem hwl] at hc
  rw [hsel]
  unfold PV_B3P_FrontierOutcome226V3.frontierAt
  rw [hq]
  simp only [bind_tc_ok]
  rw [hr]
  simp only [bind_tc_ok]
  rw [hs]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a q hqb]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value row s hsb]
  simp only [bind_tc_ok]
  rw [ht]
  simp only [bind_tc_ok]
  rw [PV_B3P_NativeFieldByte226V3.complete_result _ t htb]
  simp only [← PV_B3P_EndianVerified226V3.word_bytes]
  by_cases hcan : row.val[s.val]'hsl < 2147483647#u32
  · simp only [hcan,↓reduceIte]
    rw [hc]
    rfl
  · simp only [hcan,↓reduceIte]

#print axioms complete_result
end PV_B3P_FrontierValue226
