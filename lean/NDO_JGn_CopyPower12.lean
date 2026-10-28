import NDO_JGn_CopyPower08
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_CopyPower12
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal

def start : Result (Array field.QM31 16#usize × Usize) := JGn_CopyPower08.tail
def tail : Result (Array field.QM31 16#usize × Usize) := by jgn_tail 12 start

theorem source : start=tail := by jgn_prefix 12
#print axioms source
end AspisR1.JGn_CopyPower12
end
