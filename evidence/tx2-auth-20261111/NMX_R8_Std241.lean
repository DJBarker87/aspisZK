import NMX_R7_Std241
import NFY_Part054
import NLW_StartScope
import AdapterRwScalar
set_option autoImplicit false
noncomputable section
namespace NMX_R8_Std241
open Aeneas Aeneas.Std Result AdapterRw

def ops (env : RSL.Env) : Ops :=
 {NMX_R7_Std241.ops env with op19 :=
  AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES}

theorem late (env : RSL.Env) : (ops env).op19 = ok 1520#usize :=
 AspisR1.NFY_JFs_LateConstants.size

theorem statement (env : RSL.Env) :
 aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES (ops env) = ok 1880#usize := by
 unfold aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES
 rw [late,bind_tc_ok]
 unfold aspis_statement.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES
 rw [AspisR1.AdapterRw.Scalar.add_eq 144#usize 1520#usize 1664#usize (by scalar_tac),bind_tc_ok,
  AspisR1.AdapterRw.Scalar.add_eq 1664#usize 216#usize 1880#usize (by scalar_tac)]

theorem afterstate (env : RSL.Env) :
 aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES (ops env) = ok 688#usize :=
 NLW_StartScope.proof_start _

theorem checked : Usize.checked_add 688#usize 57607#usize = some 58295#usize :=
 AspisR1.AdapterRw.Scalar.checked_add_eq _ _ _ (by scalar_tac)

theorem observer (env : RSL.Env) : AdapterRw.observer (ops env) = ok none := rfl

theorem full_range (env : RSL.Env) (T : Type) (a : Slice T) :
 (ops env).op4 () a = ok a := rfl

#print axioms late
#print axioms statement
#print axioms afterstate
#print axioms checked
#print axioms observer
#print axioms full_range
end NMX_R8_Std241
end
