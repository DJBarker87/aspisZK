import NDO_JGh_TX2_NodeViews
set_option autoImplicit false
namespace AspisR1.JGk_TX2_ZeroWindows
open Aeneas Aeneas.Std

theorem source (n : Nat) (xs : List U8) (size : xs.length=32*n)
    (windows : ∀ i,i<n → (xs.drop (32*i)).take 32=List.replicate 32 0#u8) :
    xs=List.replicate (32*n) 0#u8 := by
  induction n generalizing xs with
  | zero =>
    have h : xs=[] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    rfl
  | succ n ih =>
    have head : xs.take 32=List.replicate 32 0#u8 := by
      simpa only [Nat.mul_zero,List.drop_zero] using windows 0 (by omega)
    have tail : xs.drop 32=List.replicate (32*n) 0#u8 := by
      apply ih
      · simp only [List.length_drop]
        omega
      · intro i hi
        have h := windows (i+1) (by omega)
        simpa only [List.drop_drop,show 32+32*i=32*(i+1) from by omega] using h
    calc
      xs=xs.take 32++xs.drop 32 := (List.take_append_drop 32 xs).symm
      _=List.replicate 32 0#u8++List.replicate (32*n) 0#u8 := by rw [head,tail]
      _=List.replicate (32*(n+1)) 0#u8 := by
        rw [←List.replicate_add]
        congr 1
        omega
#print axioms source
end AspisR1.JGk_TX2_ZeroWindows
