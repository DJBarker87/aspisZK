import Port3_Wrapping
import NDO_JHi_Distinct0
import NDO_JHi_Distinct1
import NDO_JHi_Distinct2
import NDO_JHi_Distinct3
import NDO_JHi_Distinct4
import NDO_JHi_Distinct5
import NDO_JHi_Distinct6
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHi_Distinct
open Aeneas Aeneas.Std Result ControlFlow
open _root_.AdapterRw
open JHi_DistinctAccounts
theorem step0 (base : Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0.body (JHd_KeyStd.install base) value 0#usize=ok (cont 1#usize) := by
  unfold r1_pool_adapter.owned.require_distinct_accounts_loop0.body
  rw [if_pos (by decide),JHi_Distinct0.source,bind_tc_ok]
  have inc : Usize.wrapping_add 0#usize 1#usize=1#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 0#usize (by decide)
  simp only [lift,inc,bind_tc_ok]
#print axioms step0
theorem step1 (base : Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0.body (JHd_KeyStd.install base) value 1#usize=ok (cont 2#usize) := by
  unfold r1_pool_adapter.owned.require_distinct_accounts_loop0.body
  rw [if_pos (by decide),JHi_Distinct1.source,bind_tc_ok]
  have inc : Usize.wrapping_add 1#usize 1#usize=2#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 1#usize (by decide)
  simp only [lift,inc,bind_tc_ok]
#print axioms step1
theorem step2 (base : Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0.body (JHd_KeyStd.install base) value 2#usize=ok (cont 3#usize) := by
  unfold r1_pool_adapter.owned.require_distinct_accounts_loop0.body
  rw [if_pos (by decide),JHi_Distinct2.source,bind_tc_ok]
  have inc : Usize.wrapping_add 2#usize 1#usize=3#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 2#usize (by decide)
  simp only [lift,inc,bind_tc_ok]
#print axioms step2
theorem step3 (base : Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0.body (JHd_KeyStd.install base) value 3#usize=ok (cont 4#usize) := by
  unfold r1_pool_adapter.owned.require_distinct_accounts_loop0.body
  rw [if_pos (by decide),JHi_Distinct3.source,bind_tc_ok]
  have inc : Usize.wrapping_add 3#usize 1#usize=4#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 3#usize (by decide)
  simp only [lift,inc,bind_tc_ok]
#print axioms step3
theorem step4 (base : Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0.body (JHd_KeyStd.install base) value 4#usize=ok (cont 5#usize) := by
  unfold r1_pool_adapter.owned.require_distinct_accounts_loop0.body
  rw [if_pos (by decide),JHi_Distinct4.source,bind_tc_ok]
  have inc : Usize.wrapping_add 4#usize 1#usize=5#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 4#usize (by decide)
  simp only [lift,inc,bind_tc_ok]
#print axioms step4
theorem step5 (base : Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0.body (JHd_KeyStd.install base) value 5#usize=ok (cont 6#usize) := by
  unfold r1_pool_adapter.owned.require_distinct_accounts_loop0.body
  rw [if_pos (by decide),JHi_Distinct5.source,bind_tc_ok]
  have inc : Usize.wrapping_add 5#usize 1#usize=6#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 5#usize (by decide)
  simp only [lift,inc,bind_tc_ok]
#print axioms step5
theorem step6 (base : Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0.body (JHd_KeyStd.install base) value 6#usize=ok (cont 7#usize) := by
  unfold r1_pool_adapter.owned.require_distinct_accounts_loop0.body
  rw [if_pos (by decide),JHi_Distinct6.source,bind_tc_ok]
  have inc : Usize.wrapping_add 6#usize 1#usize=7#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 6#usize (by decide)
  simp only [lift,inc,bind_tc_ok]
#print axioms step6
theorem step7 (base : Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0.body (JHd_KeyStd.install base) value 7#usize=ok (done none) := by
  rfl
#print axioms step7
theorem source (base : Ops) :
    r1_pool_adapter.owned.require_distinct_accounts (JHd_KeyStd.install base) value=ok (.Ok ()) := by
  unfold r1_pool_adapter.owned.require_distinct_accounts
  have run : r1_pool_adapter.owned.require_distinct_accounts_loop0 (JHd_KeyStd.install base) value 0#usize=ok none := by
    conv_lhs =>
      unfold r1_pool_adapter.owned.require_distinct_accounts_loop0
      rw [Aeneas.Std.loop.eq_def]
    simp only [step0,bind_tc_ok]
    conv_lhs =>
      unfold r1_pool_adapter.owned.require_distinct_accounts_loop0
      rw [Aeneas.Std.loop.eq_def]
    simp only [step1,bind_tc_ok]
    conv_lhs =>
      unfold r1_pool_adapter.owned.require_distinct_accounts_loop0
      rw [Aeneas.Std.loop.eq_def]
    simp only [step2,bind_tc_ok]
    conv_lhs =>
      unfold r1_pool_adapter.owned.require_distinct_accounts_loop0
      rw [Aeneas.Std.loop.eq_def]
    simp only [step3,bind_tc_ok]
    conv_lhs =>
      unfold r1_pool_adapter.owned.require_distinct_accounts_loop0
      rw [Aeneas.Std.loop.eq_def]
    simp only [step4,bind_tc_ok]
    conv_lhs =>
      unfold r1_pool_adapter.owned.require_distinct_accounts_loop0
      rw [Aeneas.Std.loop.eq_def]
    simp only [step5,bind_tc_ok]
    conv_lhs =>
      unfold r1_pool_adapter.owned.require_distinct_accounts_loop0
      rw [Aeneas.Std.loop.eq_def]
    simp only [step6,bind_tc_ok]
    conv_lhs =>
      unfold r1_pool_adapter.owned.require_distinct_accounts_loop0
      rw [Aeneas.Std.loop.eq_def]
    simp only [step7,bind_tc_ok]
  rw [run,bind_tc_ok]
#print axioms source
end AspisR1.JHi_Distinct
end
