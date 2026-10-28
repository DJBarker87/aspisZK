import NDO_JGn_PrefixEval
import NDO_JGl_NumericData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_CopyPower04
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal

def start : Result (Array field.QM31 16#usize × Usize) := pattern_values_literal_loop0 JFu_TerminalPrefix.challenges.lambda (Array.repeat 16#usize field.QM31.ZERO) JFu_TerminalPrefix.challenges.lambda 0#usize
def tail : Result (Array field.QM31 16#usize × Usize) := by jgn_tail 4 start

theorem source : start=tail := by jgn_prefix 4
#print axioms source
end AspisR1.JGn_CopyPower04
end
