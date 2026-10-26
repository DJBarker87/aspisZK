import JFs_LateConstants
set_option autoImplicit false
namespace AspisR1.JFs_PublicSize
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal

theorem payment_offset : PAYMENT_STATEMENT_OFFSET=ok 1664#usize := by
  unfold PAYMENT_STATEMENT_OFFSET LATE_STATEMENT_OFFSET
  rw [JFs_LateConstants.size]
  simp only [bind_tc_ok]
  obtain ⟨z,call,value⟩:=WP.spec_imp_exists
    (Usize.add_spec (x:=144#usize) (y:=1520#usize) (by scalar_tac))
  have same : z=1664#usize := by scalar_tac
  exact same ▸ call

theorem bytes : POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES=ok 1880#usize := by
  unfold POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES
  rw [JFs_LateConstants.size]
  simp only [bind_tc_ok]
  step*

#print axioms payment_offset
#print axioms bytes
end AspisR1.JFs_PublicSize
