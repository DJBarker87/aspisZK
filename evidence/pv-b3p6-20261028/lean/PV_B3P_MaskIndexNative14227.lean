import PV_B3P_MaskNative14227
namespace PV_B3P_Correct14227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding10227 PV_B3P_Success227
set_option autoImplicit false

def mask_index14 (index : Nat) (bound : index < 16) : Usize := Usize.ofNatCore index (by
  have hb := Usize.cMax_bound_concrete.1
  scalar_tac)

theorem mask_index_value14 (index : Nat) (bound : index < 16) :
    (mask_index14 index bound).val = index := rfl

theorem mask_read_source_index14 (values : Array aspis_core.field.QM31 16#usize)
    (index : Nat) (bound : index < 16) :
    mask_read10 values index = Array.index_usize values (mask_index14 index bound) := by
  have alternatives : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 := by omega
  rcases alternatives with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst index; rfl

theorem mask_walk_indices14 (mask : U16) (allowed : MaskAllowed mask)
    (index : Nat) (member : index ∈ PV_B3P_Mask227.walk 16 mask.val) : index < 16 := by
  rcases allowed with h|h|h|h|h|h|h
  all_goals subst mask
  · change index ∈ PV_B3P_Mask227.walk 16 1749 at member
    rw [PV_B3P_Mask227.walk_1749] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
  · change index ∈ PV_B3P_Mask227.walk 16 2048 at member
    rw [PV_B3P_Mask227.walk_2048] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
  · change index ∈ PV_B3P_Mask227.walk 16 2049 at member
    rw [PV_B3P_Mask227.walk_2049] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
  · change index ∈ PV_B3P_Mask227.walk 16 4097 at member
    rw [PV_B3P_Mask227.walk_4097] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
  · change index ∈ PV_B3P_Mask227.walk 16 6144 at member
    rw [PV_B3P_Mask227.walk_6144] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
  · change index ∈ PV_B3P_Mask227.walk 16 6145 at member
    rw [PV_B3P_Mask227.walk_6145] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
  · change index ∈ PV_B3P_Mask227.walk 16 26214 at member
    rw [PV_B3P_Mask227.walk_26214] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
#print axioms mask_index_value14
#print axioms mask_read_source_index14
#print axioms mask_walk_indices14
end PV_B3P_Correct14227
