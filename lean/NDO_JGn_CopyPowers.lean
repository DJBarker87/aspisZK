import NDO_JGn_CopyPower16
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_CopyPowers
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal

def returned : Array field.QM31 16#usize × Usize := by
  jgn_return JGn_CopyPower16.tail
def powers : Array field.QM31 16#usize := returned.1

theorem source : pattern_values_literal_loop0 JFu_TerminalPrefix.challenges.lambda
    (Array.repeat 16#usize field.QM31.ZERO) JFu_TerminalPrefix.challenges.lambda 0#usize=
    ok (powers,16#usize) := by
  have joined := JGn_CopyPower04.source.trans (JGn_CopyPower08.source.trans
    (JGn_CopyPower12.source.trans JGn_CopyPower16.source))
  refine joined.trans ?_
  jgn_eval
#print axioms source
end AspisR1.JGn_CopyPowers
end
