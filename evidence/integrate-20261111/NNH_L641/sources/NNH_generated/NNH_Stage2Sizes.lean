import NNH_Stage2SourceConfiguration
import NNH_RequestSize
set_option autoImplicit false
noncomputable section
namespace NNH_Stage2Sizes
open Aeneas Aeneas.Std AspisR1 AdapterRw

theorem add (x y z : Usize) (eq : x.val+y.val=z.val) (small : x.val+y.val≤65536) :
 (x+y : Result Usize)=.ok z := by
 have run := Port4A_ReaderInstall.add_value x y small
 have same : Usize.ofNat (x.val+y.val) (by scalar_tac)=z := by
  apply UScalar.eq_of_val_eq
  scalar_tac
 exact run.trans (congrArg Result.ok same)

theorem afterstate (ops : Ops) :
 aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops=.ok 688#usize := by
 unfold aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
  aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
 exact add _ _ _ (by scalar_tac) (by scalar_tac)

theorem checkedEnd : Usize.checked_add 688#usize 57607#usize=some 58295#usize := by
 unfold Usize.checked_add core.num.checked_add_UScalar
 rw [add _ _ 58295#usize (by scalar_tac) (by scalar_tac)]
 rfl

theorem statement (ops : Ops) (late : ops.op19=.ok 1520#usize) :
 aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES ops=.ok 1880#usize := by
 unfold aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES
 rw [late]
 simp only [bind_tc_ok]
 rw [add _ _ 1664#usize (by scalar_tac) (by scalar_tac)]
 simp only [bind_tc_ok]
 unfold aspis_statement.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES
 exact add _ _ _ (by scalar_tac) (by scalar_tac)
#print axioms add
#print axioms afterstate
#print axioms checkedEnd
#print axioms statement
end NNH_Stage2Sizes
