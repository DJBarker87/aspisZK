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
  interval_cases index <;> rfl

theorem mask_walk_indices14 (mask : U16) (allowed : MaskAllowed mask)
    (index : Nat) (member : index ∈ PV_B3P_Mask227.walk 16 mask.val) : index < 16 := by
  rcases allowed with h|h|h|h|h|h|h
  all_goals subst mask
  · rw [PV_B3P_Mask227.walk_1749] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
  · rw [PV_B3P_Mask227.walk_2048] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
  · rw [PV_B3P_Mask227.walk_2049] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
  · rw [PV_B3P_Mask227.walk_4097] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
  · rw [PV_B3P_Mask227.walk_6144] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
  · rw [PV_B3P_Mask227.walk_6145] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
  · rw [PV_B3P_Mask227.walk_26214] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
#print axioms mask_index_value14
#print axioms mask_read_source_index14
#print axioms mask_walk_indices14
end PV_B3P_Correct14227
