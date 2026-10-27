import JFy_PreparedSteps
import FIw_CopyEndpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_CopyEndpoint
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_copy_terminal

@[step] theorem source (values weights : Array field.QM31 2#usize)
    (e : CompiledPoolV1PairForestEndpoint) (tag weight : U32)
    (patterns : Array field.QM31 14#usize) (s : Selectors)
    (hv : canonical values) (hw : canonical weights) (hp : canonical patterns)
    (hh : canonical s.high) (hl : canonical s.low) (hr : e.row.val<1024)
    (hs : e.slot.val<2) (hpat : e.pattern.val<14) (ht : tag.val<2147483647) :
    accumulate_endpoint values weights e tag weight patterns s ⦃ out => canonical out.1 ∧ canonical out.2 ⦄ := by
  have rowv := core.convert.num.FromUsizeU16.from_val_eq e.row
  have slotv := core.convert.num.FromUsizeU8.from_val_eq e.slot
  have patv := core.convert.num.FromUsizeU8.from_val_eq e.pattern
  unfold accumulate_endpoint
  step* <;> first | assumption | scalar_tac
#print axioms source
end AspisR1.JGa_CopyEndpoint
end
