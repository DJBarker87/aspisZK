import PV_B3P_MaskCount132
namespace PV_B3P_MaskCapacity132
open PV_B3P_MaskScan132 PV_B3P_MaskCount132
set_option autoImplicit false

instance (r c : Nat) : Decidable (PV_B3P_MaskShape132.localUsed r c) := by
  unfold PV_B3P_MaskShape132.localUsed
  infer_instance
instance (r c : Nat) : Decidable (PV_B3P_MaskModel132.valueUsed r c) := by
  unfold PV_B3P_MaskModel132.valueUsed
  infer_instance

theorem pick_path (r c : Nat) (lo : 912 ≤ r) (hi : r < 1008) :
    pick r c = decide (¬ PV_B3P_MaskShape132.localUsed r c) := by
  apply Bool.eq_iff_iff.mpr
  simp only [pick,decide_eq_true_eq,PV_B3P_MaskModel132.free]
  simp [show ¬r < 912 by omega,hi]

theorem pick_value (r c : Nat) (lo : 1008 ≤ r) :
    pick r c = decide (¬ PV_B3P_MaskModel132.valueUsed (r-1008) c) := by
  apply Bool.eq_iff_iff.mpr
  simp only [pick,decide_eq_true_eq,PV_B3P_MaskModel132.free]
  simp [show ¬r < 912 by omega,show ¬r < 1008 by omega]

theorem path_block (c b : Nat) (hb : b < 6) :
    number pick c (912+16*b) 16 = if c ≤ 8 then 8 else 12 := by
  simp only [number]
  simp (disch := omega) only [pick_path,decide_eq_true_eq]
  simp [PV_B3P_MaskShape132.localUsed,Nat.add_mod,Nat.mul_mod]
  by_cases h : c ≤ 8
  · have hn : ¬8 < c := by omega
    simp [h,hn]
  · have hn : 8 < c := by omega
    simp [h,hn]

theorem value_formula (c : Nat) :
    number pick c 1008 16 = 10*(if 10 < c then 1 else 0) +
      (if 3 ≤ c then 1 else 0) + (if 1 < c then 1 else 0) +
      (if 10 ≤ c then 1 else 0) + 3 := by
  simp only [number]
  simp (disch := omega) only [pick_value,decide_eq_true_eq]
  simp only [PV_B3P_MaskModel132.valueUsed]
  norm_num only
  omega

theorem value_block (c : Nat) :
    number pick c 1008 16 =
      if c < 2 then 3 else if c < 3 then 4 else if c < 10 then 5 else if c ≤ 10 then 6 else 16 := by
  rw [value_formula]
  split_ifs <;> omega

theorem per_column (c : Nat) :
    (rows pick c 0 1024).length =
      171 + (if c ≤ 8 then 48 else 72) +
        (if c < 2 then 3 else if c < 3 then 4 else if c < 10 then 5 else if c ≤ 10 then 6 else 16) := by
  rw [length_rows]
  have ha := blocks pick c 0 57 3 (fun b hb => by simpa using padding_block c b hb)
  have hb := blocks pick c 912 6 (if c ≤ 8 then 8 else 12) (fun b hb => path_block c b hb)
  have hsplit : 1024 = 912+(96+16) := by omega
  rw [hsplit,number_add,number_add]
  change number pick c 0 912 + (number pick c 912 96 + number pick c 1008 16) = _
  rw [show number pick c 0 912 = 171 from ha]
  rw [show number pick c 912 96 = 6*(if c ≤ 8 then 8 else 12) from hb,value_block]
  split <;> simp_all <;> omega

theorem full_count : (columns pick 0 16).length = 3803 := by
  simp only [columns,List.length_append,List.length_nil,per_column]
  rfl

#print axioms pick_path
#print axioms pick_value
#print axioms path_block
#print axioms value_formula
#print axioms value_block
#print axioms per_column
#print axioms full_count
end PV_B3P_MaskCapacity132
