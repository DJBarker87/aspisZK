import NDO_JGn_CopyPower12
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_CopyPower16
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal

def start : Result (Array field.QM31 16#usize × Usize) := JGn_CopyPower12.tail
def tail : Result (Array field.QM31 16#usize × Usize) := by jgn_tail 16 start

theorem source : start=tail := by jgn_prefix 16
#print axioms source
end AspisR1.JGn_CopyPower16
end
