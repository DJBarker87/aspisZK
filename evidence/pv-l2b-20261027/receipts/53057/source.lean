import PV_L2B_Rejection
set_option autoImplicit false
namespace PV_L2B_Cursor
-- Absolute consumed-word cursor; initial source word=8 triggers the first refill.
def offset (consumed : Nat) : Nat := 4*(consumed % 8)
def blockIndex (consumed : Nat) : Nat := consumed/8
def afterWord (consumed : Nat) : Nat := consumed%8+1
def consumed (rejections : List Nat) : Nat := (rejections.map (fun r => r+1)).sum
theorem offset_zero : offset 0 = 0 := rfl
#print axioms offset_zero
theorem offset_bound (n : Nat) : offset n < 32 := by unfold offset; have := Nat.mod_lt n (by decide : 0<8); omega
#print axioms offset_bound
theorem last_byte_bound (n : Nat) : offset n + 3 < 32 := by unfold offset; have := Nat.mod_lt n (by decide : 0<8); omega
#print axioms last_byte_bound
theorem read_word_bound (n : Nat) : afterWord n ≤ 8 := by unfold afterWord; have := Nat.mod_lt n (by decide : 0<8); omega
#print axioms read_word_bound
end PV_L2B_Cursor
