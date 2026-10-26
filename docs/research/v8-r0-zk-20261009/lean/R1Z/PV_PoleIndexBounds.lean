import Std
set_option autoImplicit false
namespace R1Z.PV_PoleIndexBounds

theorem mask_word (row : Nat) (bound : row < 1024) : row / 16 < 64 := by omega

theorem mask_bit (row : Nat) : row % 16 < 16 := Nat.mod_lt _ (by decide)

theorem row_reconstruction (row : Nat) : (row / 16)*16 + row%16 = row := by omega

theorem successor (row : Nat) (bound : row < 1024) : row+1 ≤ 1024 := by omega

theorem remaining_decreases (row : Nat) (bound : row < 1024) :
    1024-(row+1)<1024-row := by omega

#print axioms mask_word
#print axioms mask_bit
#print axioms row_reconstruction
#print axioms successor
#print axioms remaining_decreases
end R1Z.PV_PoleIndexBounds
