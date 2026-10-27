import FIy_FrontierMeaning
import R0P.EmptyRoots
set_option autoImplicit false
namespace AspisR1.FIz_EmptyRoots
open Aeneas Aeneas.Std
open FIq_Native

theorem table (level : Fin 21) (j : Fin 8) :
    ((FIy_FrontierMeaning.roots level.val).val[j.val]?).getD 0#u32 |>.val =
      R0P.emptyRootsNat level j := by
  fin_cases level <;> fin_cases j <;>
    rfl
#print axioms table
end AspisR1.FIz_EmptyRoots
