import PV_B3P_MaskShape132
namespace PV_B3P_MaskPath132
open PV_B3P_MaskShape132
set_option autoImplicit false

theorem local_to_path (row column : Nat) (lo : 912 ≤ row) (hi : row < 1008)
    (h : localUsed row column) : pathUsed row column := by
  unfold localUsed at h
  rcases h with ⟨h,hc⟩ | h | h | h | h
  · rcases h with h | h | h | h
    · refine ⟨4*((row-912)/16),by omega,Or.inl ⟨?_,hc⟩⟩
      unfold base
      omega
    · refine ⟨4*((row-912)/16)+1,by omega,Or.inl ⟨?_,hc⟩⟩
      unfold base
      omega
    · refine ⟨4*((row-912)/16)+2,by omega,Or.inl ⟨?_,hc⟩⟩
      unfold base
      omega
    · refine ⟨4*((row-912)/16)+3,by omega,Or.inl ⟨?_,hc⟩⟩
      unfold base
      omega
  · refine ⟨4*((row-912)/16),by omega,Or.inr ?_⟩
    unfold base
    omega
  · refine ⟨4*((row-912)/16)+1,by omega,Or.inr ?_⟩
    unfold base
    omega
  · refine ⟨4*((row-912)/16)+2,by omega,Or.inr ?_⟩
    unfold base
    omega
  · refine ⟨4*((row-912)/16)+3,by omega,Or.inr ?_⟩
    unfold base
    omega

theorem used_iff (row column : Nat) (lo : 912 ≤ row) (hi : row < 1008) :
    pathUsed row column ↔ localUsed row column :=
  ⟨path_to_local row column,local_to_path row column lo hi⟩
#print axioms local_to_path
#print axioms used_iff
end PV_B3P_MaskPath132
