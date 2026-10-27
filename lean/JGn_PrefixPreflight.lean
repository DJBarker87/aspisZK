import JGn_PrefixEval
import JGl_NumericData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_PrefixPreflight
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal

def start : Result (Array field.QM31 16#usize × Usize) :=
  pattern_values_literal_loop0 field.QM31.ONE (Array.repeat 16#usize field.QM31.ZERO) field.QM31.ONE 14#usize
def tail : Result (Array field.QM31 16#usize × Usize) := by jgn_tail 15 start

theorem source : start=tail := by jgn_prefix 15
#print axioms source
end AspisR1.JGn_PrefixPreflight
end
