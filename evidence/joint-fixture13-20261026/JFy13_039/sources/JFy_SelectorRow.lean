import JFy_Specs
import FIq_Native13
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_SelectorRow
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_copy_terminal

@[spec] theorem source (s : Selectors) (row : Usize) (bound : row.val<1024)
    (hh : canonical s.high) (hl : canonical s.low) :
    Selectors.row s row ⦃ out => Canon out ⦄ := by
  unfold Selectors.row
  step* <;> first | assumption | scalar_tac
#print axioms source
end AspisR1.JFy_SelectorRow
end
