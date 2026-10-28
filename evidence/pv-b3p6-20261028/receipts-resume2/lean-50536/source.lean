import PV_B3P_LateRegions226
import PV_B3P_FrontierValue226
import PV_B3P_NestedOffset226V3
namespace PV_B3P_LateValue226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_ByteLayout226V3
set_option autoImplicit false
theorem recipient (p : reference226.OwnedPublic) (i : Usize)
    (hw : p.withdrawal = false)
    (lo : 70 ≤ i.val) (hi : i.val < 102) :
    reference226.byte_at p i =
      if (p.recipient.val)[(i.val-70)/4]?.getD 0#u32 < 2147483647#u32 then
        .ok (.Ok ((fields (p.recipient.val))[i.val-70]?.getD 0#u8))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  have hoff : (Usize.wrapping_sub i 70#usize).val = i.val-70 := by
    repeat first
      | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
      | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
    scalar_tac
  rw [PV_B3P_LateRegions226.recipient p i hw lo hi]
  rw [PV_B3P_DigestValue226V3.complete_result _ _ (by
    rw [hoff]
    scalar_tac)]
  simp only [hoff]
#print axioms recipient
theorem change (p : reference226.OwnedPublic) (i : Usize)
    (lo : (if p.withdrawal then 70 else 102) ≤ i.val) (hi : i.val < (if p.withdrawal then 102 else 134)) :
    reference226.byte_at p i =
      if (p.change.val)[(i.val-(if p.withdrawal then 70 else 102))/4]?.getD 0#u32 < 2147483647#u32 then
        .ok (.Ok ((fields (p.change.val))[i.val-(if p.withdrawal then 70 else 102)]?.getD 0#u8))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  have hoff : (Usize.wrapping_sub i (if p.withdrawal then 70#usize else 102#usize)).val = i.val-(if p.withdrawal then 70 else 102) := by
    cases hw : p.withdrawal <;> simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    all_goals
      repeat first
        | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
        | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
      scalar_tac
  rw [PV_B3P_LateRegions226.change p i lo hi]
  rw [PV_B3P_DigestValue226V3.complete_result _ _ (by
    rw [hoff]
    cases hw : p.withdrawal <;> simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢ <;> scalar_tac)]
  simp only [hoff]
#print axioms change
theorem frontier (p : reference226.OwnedPublic) (i : Usize)
    (lo : (if p.withdrawal then 115 else 143) ≤ i.val) (hi : i.val < (if p.withdrawal then 755 else 783)) :
    reference226.byte_at p i =
      if (PV_B3P_ByteLayout226V3.frontier p.frontier)[(i.val-(if p.withdrawal then 115 else 143))/4]?.getD 0#u32 < 2147483647#u32 then
        .ok (.Ok ((fields (PV_B3P_ByteLayout226V3.frontier p.frontier))[i.val-(if p.withdrawal then 115 else 143)]?.getD 0#u8))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  have hoff : (Usize.wrapping_sub i (if p.withdrawal then 115#usize else 143#usize)).val = i.val-(if p.withdrawal then 115 else 143) := by
    cases hw : p.withdrawal <;> simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    all_goals
      repeat first
        | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
        | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
      scalar_tac
  rw [PV_B3P_LateRegions226.frontier p i lo hi]
  rw [PV_B3P_FrontierValue226.complete_result _ _ (by
    rw [hoff]
    cases hw : p.withdrawal <;> simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢ <;> scalar_tac)]
  simp only [hoff]
#print axioms frontier
theorem next_root (p : reference226.OwnedPublic) (i : Usize)
    (lo : (if p.withdrawal then 755 else 783) ≤ i.val) (hi : i.val < (if p.withdrawal then 787 else 815)) :
    reference226.byte_at p i =
      if (p.next_root.val)[(i.val-(if p.withdrawal then 755 else 783))/4]?.getD 0#u32 < 2147483647#u32 then
        .ok (.Ok ((fields (p.next_root.val))[i.val-(if p.withdrawal then 755 else 783)]?.getD 0#u8))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  have hoff : (Usize.wrapping_sub (Usize.wrapping_sub i (if p.withdrawal then 115#usize else 143#usize)) 640#usize).val = i.val-(if p.withdrawal then 755 else 783) := by
    cases hw : p.withdrawal <;> simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    all_goals
      repeat first
        | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
        | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
      scalar_tac
  rw [PV_B3P_LateRegions226.next_root p i lo hi]
  rw [PV_B3P_DigestValue226V3.complete_result _ _ (by
    rw [hoff]
    cases hw : p.withdrawal <;> simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢ <;> scalar_tac)]
  simp only [hoff]
#print axioms next_root
theorem next_frontier (p : reference226.OwnedPublic) (i : Usize)
    (lo : (if p.withdrawal then 787 else 815) ≤ i.val) (hi : i.val < (if p.withdrawal then 1427 else 1455)) :
    reference226.byte_at p i =
      if (PV_B3P_ByteLayout226V3.frontier p.next_frontier)[(i.val-(if p.withdrawal then 787 else 815))/4]?.getD 0#u32 < 2147483647#u32 then
        .ok (.Ok ((fields (PV_B3P_ByteLayout226V3.frontier p.next_frontier))[i.val-(if p.withdrawal then 787 else 815)]?.getD 0#u8))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  have hoff : (Usize.wrapping_sub (Usize.wrapping_sub i (if p.withdrawal then 115#usize else 143#usize)) 672#usize).val = i.val-(if p.withdrawal then 787 else 815) := by
    cases hw : p.withdrawal <;> simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    all_goals
      repeat first
        | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
        | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
      scalar_tac
  rw [PV_B3P_LateRegions226.next_frontier p i lo hi]
  rw [PV_B3P_FrontierValue226.complete_result _ _ (by
    rw [hoff]
    cases hw : p.withdrawal <;> simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢ <;> scalar_tac)]
  simp only [hoff]
#print axioms next_frontier
end PV_B3P_LateValue226
