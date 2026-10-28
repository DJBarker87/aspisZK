import Port3_Wrapping
import NDO_JHi_DistinctAccounts
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHi_Distinct1
open Aeneas Aeneas.Std Result ControlFlow
open _root_.AdapterRw
open JHi_DistinctAccounts
attribute [local irreducible] JHb_Header.account JFx_NativeBytes.publicInput JFx_NativeBytes.checkpoint
theorem step0 (base : Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body (JHd_KeyStd.install base)
      value 1#usize 0#usize=ok (cont 1#usize) := by
  have inc : Usize.wrapping_add 0#usize 1#usize=1#usize := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment 0#usize (by decide)
  unfold r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body
  simp only [lift,inc]
  rfl
#print axioms step0
theorem step1 (base : Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body (JHd_KeyStd.install base)
      value 1#usize 1#usize=ok (done none) := by rfl
#print axioms step1
theorem source (base : Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0 (JHd_KeyStd.install base)
      value 1#usize 0#usize=ok none := by
  conv_lhs =>
    unfold r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0
    rw [Aeneas.Std.loop.eq_def]
  simp only [step0,bind_tc_ok]
  conv_lhs =>
    unfold r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0
    rw [Aeneas.Std.loop.eq_def]
  simp only [step1,bind_tc_ok]
#print axioms source
end AspisR1.JHi_Distinct1
end
