import NDO_JHi_Authentication
import NDO_JHg_World
import NDO_JHi_Guards
import NDO_JHi_CheckpointGuard
import NDO_JHi_AccountReads
import NDO_JHi_Distinct
import NDO_JHb_Guards
import JGx_EntryReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHi_AuthenticationPrefix
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers JHg_World
open _root_.AdapterRw
attribute [local irreducible] e2 JHb_Header.account JHg_DataMaster.value
attribute [local irreducible] r1_pool_adapter.owned.require_readonly_buffer
  r1_pool_adapter.owned.require_verifier_checkpoint r1_pool_adapter.owned.require_readonly_account
  r1_pool_adapter.owned.require_distinct_accounts r1_pool_adapter.owned.OwnedAccount.data

theorem source (base : Ops) (lane : U8) (slot : U64) :
    r1_pool_adapter.owned.authenticate_asq8_accounts (JHd_KeyStd.install base)
      CPH_Program.verifier (e2.second secondSizes) JHb_Programs.pool lane slot=
    JHi_Authentication.afterRead (JHd_KeyStd.install base) CPH_Program.verifier JHb_Programs.pool lane slot
      (e2.snapshot 1 384 384) (e2.snapshot 2 192 192) (e2.snapshot 3 768 768)
      (e2.snapshot 4 128 256) (e2.snapshot 5 192 320) := by
  have count:=JGx_EntryReads.count e2
  have i0 : Slice.index_usize (e2.second secondSizes) 0#usize=ok (e2.snapshot 0 58295 58295) := rfl
  have i1 : Slice.index_usize (e2.second secondSizes) 1#usize=ok (e2.snapshot 1 384 384) := rfl
  have i2 : Slice.index_usize (e2.second secondSizes) 2#usize=ok (e2.snapshot 2 192 192) := rfl
  have i3 : Slice.index_usize (e2.second secondSizes) 3#usize=ok (e2.snapshot 3 768 768) := rfl
  have i4 : Slice.index_usize (e2.second secondSizes) 4#usize=ok (e2.snapshot 4 128 256) := rfl
  have i5 : Slice.index_usize (e2.second secondSizes) 5#usize=ok (e2.snapshot 5 192 320) := rfl
  have i6 : Slice.index_usize (e2.second secondSizes) 6#usize=ok (e2.snapshot 6 1768 1768) := rfl
  unfold r1_pool_adapter.owned.authenticate_asq8_accounts
  rw [count,if_pos rfl,i0,bind_tc_ok,i1,bind_tc_ok,i2,bind_tc_ok,i3,bind_tc_ok,
    i4,bind_tc_ok,i5,bind_tc_ok,i6,bind_tc_ok]
  rw [JHi_Guards.proof,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [JHi_CheckpointGuard.source,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [JHi_Guards.master,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [JHi_Guards.forest,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [JHi_Guards.lane,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [show Array.make 7#usize [e2.snapshot 0 58295 58295,e2.snapshot 1 384 384,
    e2.snapshot 2 192 192,e2.snapshot 3 768 768,e2.snapshot 4 128 256,
    e2.snapshot 5 192 320,e2.snapshot 6 1768 1768]=JHi_DistinctAccounts.value from rfl,
    JHi_Distinct.source,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [JHi_AccountReads.master,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  unfold JHi_Authentication.afterRead
  apply congrArg (fun k => (JHd_KeyStd.install base).op48 JHg_DataMaster.value >>= k)
  funext result
  cases result <;> simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  all_goals rfl
#print axioms source
end AspisR1.JHi_AuthenticationPrefix
end
