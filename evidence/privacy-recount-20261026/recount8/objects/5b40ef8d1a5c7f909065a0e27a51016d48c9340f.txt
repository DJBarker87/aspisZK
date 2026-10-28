import PV_B3P_Regions226V3
import PV_B3P_IndexLane226
import PV_B3P_NativeFieldByte226V3
import PV_B3P_Offset226V3
namespace PV_B3P_ScalarValue226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_ByteLayout226V3
set_option autoImplicit false

theorem word_byte (v : U32) (j : Usize) (hj : j.val < 4) :
    reference226.field_byte v j =
      if v < 2147483647#u32 then .ok (.Ok ((fields [v])[j.val]?.getD 0#u8))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  rw [PV_B3P_NativeFieldByte226V3.complete_result v j hj]
  simp only [fields,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    ← PV_B3P_EndianVerified226V3.word_bytes]
  have hb : j.val < (wordBytes v).length := by
    simpa only [wordBytes,List.length_cons,List.length_nil] using hj
  rw [List.getElem?_eq_getElem hb]
  rfl

theorem asset (p : reference226.OwnedPublic) (i : Usize)
    (lo : 65 ≤ i.val) (hi : i.val < 69) :
    reference226.byte_at p i =
      if p.asset_id < 2147483647#u32 then
        .ok (.Ok ((fields [p.asset_id])[i.val-65]?.getD 0#u8))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  have hoff := PV_B3P_Offset226V3.sub_value i 65#usize (by simpa using lo)
  rw [PV_B3P_Regions226V3.asset p i lo hi]
  rw [word_byte _ _ (by rw [hoff]; scalar_tac)]
  simpa only [hoff, show (65#usize).val = 65 from rfl]

theorem amount (p : reference226.OwnedPublic) (i : Usize) (hw : p.withdrawal = true)
    (lo : 103 ≤ i.val) (hi : i.val < 107) :
    reference226.byte_at p i =
      if p.withdrawal_amount < 2147483647#u32 then
        .ok (.Ok ((fields [p.withdrawal_amount])[i.val-103]?.getD 0#u8))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  have hoff := PV_B3P_Offset226V3.sub_value i 103#usize (by simpa using lo)
  rw [PV_B3P_ScalarRegions226.amount p i hw lo hi]
  rw [word_byte _ _ (by rw [hoff]; scalar_tac)]
  simpa only [hoff, show (103#usize).val = 103 from rfl]

theorem index_list (v : U64) (j : Usize) (hj : j.val < 8) :
    PV_B3P_ScalarRegions226.indexLane v j = (indexBytes v)[j.val]?.getD 0#u8 := by
  have hb : j.val < (indexBytes v).length := by
    simpa only [indexBytes,List.length_cons,List.length_nil] using hj
  rw [PV_B3P_EndianVerified226V3.index_bytes]
  rw [List.getElem?_eq_getElem (by rw [(core.num.U64.to_le_bytes v).property]; simpa using hj)]
  exact PV_B3P_IndexLane226.native_value v j hj

theorem index (p : reference226.OwnedPublic) (i : Usize)
    (lo : (if p.withdrawal then 107 else 135) ≤ i.val)
    (hi : i.val < (if p.withdrawal then 115 else 143)) :
    reference226.byte_at p i = .ok (.Ok
      ((indexBytes p.next_pair_index)[i.val-(if p.withdrawal then 107 else 135)]?.getD 0#u8)) := by
  have hoff : (Usize.wrapping_sub i (if p.withdrawal then 107#usize else 135#usize)).val =
      i.val-(if p.withdrawal then 107 else 135) := by
    cases hw : p.withdrawal <;>
      simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢ <;>
      rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)] <;> rfl
  rw [PV_B3P_ScalarRegions226.index p i lo hi]
  rw [index_list _ _ (by
    rw [hoff]
    cases hw : p.withdrawal <;>
      simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢ <;> omega)]
  simp only [hoff]

#print axioms word_byte
#print axioms asset
#print axioms amount
#print axioms index_list
#print axioms index
end PV_B3P_ScalarValue226
