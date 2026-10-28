import JFw_Blocks
set_option autoImplicit false
namespace AspisR1.JHm_BlockWindows
open Aeneas Aeneas.Std
/-- Select one low16-byte scalar from expanded32-byte field cells. -/
theorem source (n : Nat) (b : List U8) (len : b.length=16*n) (i : Nat) (hi : i<n) :
    ((JFw_Blocks.blocks n b).flatten.drop (32*i)).take 16=(b.drop (16*i)).take 16 := by
  induction n generalizing b i with
  | zero => omega
  | succ n ih =>
    have enough : 16≤b.length := by omega
    have first : (b.take 16).length=16 := by simp only [List.length_take];omega
    have block : (b.take 16++List.replicate 16 0#u8).length=32 := by
      rw [List.length_append,first,List.length_replicate]
    cases i with
    | zero =>
      simp only [JFw_Blocks.blocks,List.flatten_cons,Nat.mul_zero,List.drop_zero]
      rw [List.take_append,block]
      simp only [show 16-32=0 from rfl,List.take_zero,List.append_nil]
      rw [List.take_append,first]
      simp only [Nat.sub_self,List.take_zero,List.append_nil,List.take_take,Nat.min_self]
    | succ i =>
      simp only [JFw_Blocks.blocks,List.flatten_cons]
      rw [List.drop_append,block]
      rw [List.drop_eq_nil_of_le (by rw [block];omega),List.nil_append]
      rw [show 32*(i+1)-32=32*i from by omega]
      have tailLen : (b.drop 16).length=16*n := by rw [List.length_drop];omega
      rw [ih (b.drop 16) tailLen i (by omega),List.drop_drop]
      congr 2
      omega
#print axioms source
end AspisR1.JHm_BlockWindows
