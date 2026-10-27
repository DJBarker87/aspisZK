import LPa_ByteBound
set_option autoImplicit false
namespace LPa.Bytes
-- Explicit source-order little-endian limb recurrence. Four-byte bound only.
def little : List Aeneas.Std.U8 → Nat
  | [] => 0
  | b::bs => b.val + 256*little bs

theorem little_fold (bs : List Aeneas.Std.U8) : little bs = decode bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [little, decode, List.foldr_cons, ih]

theorem actual_word_loop (bs : List Aeneas.Std.U8) :
    little (bs.take 4) = XRk_Bytes.le32 bs := by
  rw [little_fold]
  rfl
#print axioms little_fold
#print axioms actual_word_loop
end LPa.Bytes
