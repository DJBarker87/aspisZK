import NDO_JHi_DistinctAccounts
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHi_Distinct0
open Aeneas Aeneas.Std Result ControlFlow
open _root_.AdapterRw
open JHi_DistinctAccounts
attribute [local irreducible] JHb_Header.account JFx_NativeBytes.publicInput JFx_NativeBytes.checkpoint
theorem step0 (base : Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body (JHd_KeyStd.install base)
      value 0#usize 0#usize=ok (done none) := by rfl
#print axioms step0
theorem source (base : Ops) :
    r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0 (JHd_KeyStd.install base)
      value 0#usize 0#usize=ok none := by
  conv_lhs =>
    unfold r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0
    rw [Aeneas.Std.loop.eq_def]
  simp only [step0,bind_tc_ok]
#print axioms source
end AspisR1.JHi_Distinct0
end
