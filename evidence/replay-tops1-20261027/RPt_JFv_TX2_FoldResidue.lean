import RPt_JFv_TX2_FoldValue
set_option autoImplicit false
namespace AspisR1.JFv_TX2_FoldResidue
open Aeneas Aeneas.Std

theorem source (n : Nat) : JFv_TX2_FoldValue.value n%2147483647=n%2147483647 := by
  have h := congrArg (fun t : Nat => t%2147483647) (Nat.mod_add_div n 2147483648)
  rw [Nat.add_mod,Nat.mul_mod,show 2147483648%2147483647=1 from rfl,one_mul] at h
  change (n%2147483648+n/2147483648)%2147483647=n%2147483647
  rw [Nat.add_mod]
  simpa only [Nat.mod_mod] using h
#print axioms source
end AspisR1.JFv_TX2_FoldResidue
