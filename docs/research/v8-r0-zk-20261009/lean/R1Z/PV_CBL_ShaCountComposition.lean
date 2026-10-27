import R1Z.PV_CBL_ShaCount
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ShaCountComposition
set_option autoImplicit false

theorem twice (old : U64) (a b : Usize) :
    (U64.wrapping_add (U64.wrapping_add old (UScalar.cast .U64 a))
      (UScalar.cast .U64 b)).val = (old.val+a.val+b.val)%2^64 := by
  rw [PV_CBL_ShaCount.wrapping_count,PV_CBL_ShaCount.wrapping_count]
  simp only [Nat.add_mod,Nat.mod_mod]

theorem commute (old : U64) (a b : Usize) :
    U64.wrapping_add (U64.wrapping_add old (UScalar.cast .U64 a)) (UScalar.cast .U64 b) =
    U64.wrapping_add (U64.wrapping_add old (UScalar.cast .U64 b)) (UScalar.cast .U64 a) := by
  apply UScalar.eq_of_val_eq
  rw [twice,twice]
  congr 1
  omega

#print axioms twice
#print axioms commute
end R1Z.PV_CBL_ShaCountComposition
