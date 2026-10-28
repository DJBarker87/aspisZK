import PV_B3P_NativeFieldByte226V3
import PV_B3P_DigestTotal226V3
import PV_B3P_LayoutCells226V3
namespace PV_B3P_DigestValue226V3
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_ByteLayout226V3
set_option autoImplicit false

theorem complete_result (a : Array U32 8#usize) (i : Usize) (hi : i.val < 32) :
    PV_B3P_DigestTotal226V3.digestAt a i =
      if (a.val[i.val / 4]?.getD 0#u32) < 2147483647#u32 then
        .ok (.Ok ((fields a.val)[i.val]?.getD 0#u8))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  obtain ⟨q,hq,hqval⟩ := UScalar.div_spec (x:=i) (y:=4#usize) (by decide)
  obtain ⟨r,hr,hrval⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (x:=i) (y:=4#usize) (by decide))
  have hqnat : q.val = i.val / 4 := by simpa using hqval
  have hrnat : r.val = i.val % 4 := by simpa using hrval
  have hqb : q.val < (8#usize).val := by
    have hn : (8#usize).val = 8 := rfl
    rw [hn,hqnat]; omega
  have hlen : q.val < a.val.length := by simpa [a.property] using hqb
  have hrb : r.val < 4 := by rw [hrnat]; omega
  have hsel : a.val[i.val / 4]?.getD 0#u32 = a.val[q.val]'hlen := by
    rw [← hqnat,List.getElem?_eq_getElem hlen]
    rfl
  have hidx : 4*q.val+r.val = i.val := by rw [hqnat,hrnat]; omega
  have hwlen : r.val < (wordBytes (a.val[q.val]'hlen)).length := by
    simpa only [wordBytes,List.length_cons,List.length_nil] using hrb
  have hcell := PV_B3P_LayoutCells226V3.fields_cell a.val q.val r.val hlen hrb
  rw [hidx,List.getElem?_eq_getElem hwlen] at hcell
  rw [hsel]
  unfold PV_B3P_DigestTotal226V3.digestAt
  rw [hq]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a q hqb]
  simp only [bind_tc_ok]
  rw [hr]
  simp only [bind_tc_ok]
  rw [PV_B3P_NativeFieldByte226V3.complete_result _ r hrb]
  rw [← PV_B3P_EndianVerified226V3.word_bytes]
  by_cases hc : (a.val[q.val]'hlen) < 2147483647#u32
  · simp only [hc,↓reduceIte]
    rw [hcell]
    rfl
  · simp only [hc,↓reduceIte]

#print axioms complete_result
end PV_B3P_DigestValue226V3
