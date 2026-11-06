import NJS_Extract.Funs
import MultiproofSortRef.Funs
import Port3_Wrapping
set_option autoImplicit false
namespace NJS_SortStep
open Aeneas Aeneas.Std Result
theorem predecessor (j : Usize) (positive : 0<j.val) :
 (Usize.wrapping_sub j 1#usize).val=j.val-1 := by
 rw [Usize.wrapping_sub_val_eq]
 have cap : 1<UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
 have bound : j.val<UScalar.size .Usize := j.bv.isLt
 change (j.val+(UScalar.size .Usize-1))%UScalar.size .Usize=j.val-1
 have eqv : j.val+(UScalar.size .Usize-1)=(j.val-1)+UScalar.size .Usize := by omega
 rw [eqv,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
#print axioms predecessor
end NJS_SortStep
