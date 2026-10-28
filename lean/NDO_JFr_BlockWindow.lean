import NDO_JFw_Frames
set_option autoImplicit false
namespace AspisR1.JFr_BlockWindow
open Aeneas Aeneas.Std

theorem source (n : Nat) (raw : List U8) (length : raw.length=16*n)
    (i : Nat) (bound : i<n) :
    (((JFw_Blocks.blocks n raw).flatten).drop (32*i)).take 16=(raw.drop (16*i)).take 16 := by
  induction n generalizing raw i with
  | zero => omega
  | succ n ih =>
    have enough : 16≤raw.length := by omega
    have headLength : (raw.take 16 ++ List.replicate 16 0#u8).length=32 := by
      simp only [List.length_append,List.length_take,List.length_replicate]
      omega
    cases i with
    | zero =>
      change ((raw.take 16 ++ List.replicate 16 0#u8) ++ (JFw_Blocks.blocks n (raw.drop 16)).flatten).take 16=raw.take 16
      rw [List.take_append]
      simp only [headLength,show 16-32=0 from rfl,List.take_zero,List.append_nil]
      rw [List.take_append]
      simp only [List.length_take,Nat.min_eq_left enough,Nat.sub_self,List.take_zero,List.append_nil,List.take_take,Nat.min_self]
    | succ i =>
      change (((raw.take 16 ++ List.replicate 16 0#u8) ++ (JFw_Blocks.blocks n (raw.drop 16)).flatten).drop (32*(i+1))).take 16=(raw.drop (16*(i+1))).take 16
      rw [List.drop_append,headLength]
      have skip : 32≤32*(i+1) := by omega
      rw [List.drop_eq_nil_of_le (by rw [headLength];omega),List.nil_append]
      have delta : 32*(i+1)-32=32*i := by omega
      rw [delta,ih (raw.drop 16) (by simp only [List.length_drop];omega) i (by omega)]
      rw [List.drop_drop]
      congr 2
      omega

#print axioms source
end AspisR1.JFr_BlockWindow
