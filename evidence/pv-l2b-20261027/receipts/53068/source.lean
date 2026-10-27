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
theorem read_word_positive (n : Nat) : 0 < afterWord n := by unfold afterWord; omega
#print axioms read_word_positive
theorem offset_period (n : Nat) : offset (n+8) = offset n := by simp [offset,Nat.add_mod]
#print axioms offset_period
theorem block_step (n : Nat) : blockIndex (n+8) = blockIndex n+1 := by simp [blockIndex,Nat.add_div_right]
#print axioms block_step
theorem word_period (n : Nat) : afterWord (n+8) = afterWord n := by simp [afterWord,Nat.add_mod]
#print axioms word_period
theorem absolute_decomposition (n : Nat) : n = 8*blockIndex n+n%8 := by unfold blockIndex; omega
#print axioms absolute_decomposition
theorem refill_iff (n : Nat) : afterWord n = 8 ↔ n%8=7 := by unfold afterWord; omega
#print axioms refill_iff
theorem first_limb_offset (r : Nat) : offset (r+1) = 4*((r+1)%8) := rfl
#print axioms first_limb_offset
theorem accepted_no_rejection_next : offset 1 = 4 := rfl
#print axioms accepted_no_rejection_next
theorem one_rejection_next : offset 2 = 8 := rfl
#print axioms one_rejection_next
theorem cursor_nil : consumed [] = 0 := rfl
#print axioms cursor_nil
theorem cursor_cons (r : Nat) (rs : List Nat) : consumed (r::rs) = r+1+consumed rs := by simp [consumed]
#print axioms cursor_cons
end PV_L2B_Cursor
