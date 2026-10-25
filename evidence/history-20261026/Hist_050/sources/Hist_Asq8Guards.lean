import S2W_EntryPrivileges
import Hist_TryGuard
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_Asq8Guards
open Aeneas Aeneas.Std Result
open AspisR1.AdapterRw.Cuts
attribute [local irreducible]
  AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
  AdapterRw.r1_pool_adapter.owned.require_readonly_buffer
  AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
  AdapterRw.r1_pool_adapter.owned.require_readonly_account
  AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
  AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry

/-- The ASQ8 path authenticates the Pool forest checkpoint and the separate
verifier checkpoint at different slots and under different program owners. -/
theorem guards (ops : AdapterRw.Ops) (verifier pool : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice Account) (lane : U8) (slot : U64)
    (out : AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts)
    (accepted : AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts ops verifier accounts pool lane slot = ok (.Ok out)) :
    ∃ master forest selected checkpoint,
      Slice.index_usize accounts 1#usize = ok master ∧
      Slice.index_usize accounts 2#usize = ok forest ∧
      Slice.index_usize accounts 3#usize = ok selected ∧
      Slice.index_usize accounts 6#usize = ok checkpoint ∧
      AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint ops checkpoint verifier false = ok (.Ok ()) ∧
      AdapterRw.r1_pool_adapter.owned.require_readonly_account ops master pool = ok (.Ok ()) ∧
      AdapterRw.r1_pool_adapter.owned.require_readonly_account ops forest pool = ok (.Ok ()) ∧
      AdapterRw.r1_pool_adapter.owned.require_readonly_account ops selected pool = ok (.Ok ()) := by
  unfold AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts at accepted
  by_cases size : Slice.len accounts = 7#usize
  · rw [if_pos size] at accepted
    obtain ⟨proof,ip,h⟩ := bind_success _ _ _ accepted
    obtain ⟨master,im,h⟩ := bind_success _ _ _ h
    obtain ⟨forest,ic,h⟩ := bind_success _ _ _ h
    obtain ⟨selected,il,h⟩ := bind_success _ _ _ h
    obtain ⟨registry,ir,h⟩ := bind_success _ _ _ h
    obtain ⟨entry,ie,h⟩ := bind_success _ _ _ h
    obtain ⟨checkpoint,iv,h⟩ := bind_success _ _ _ h
    obtain ⟨r0,g0,h⟩ := bind_success _ _ _ h
    cases r0 with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      cases h
    | Ok u0 =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨r1,g1,h⟩ := bind_success _ _ _ h
      cases r1 with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        cases h
      | Ok u1 =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        obtain ⟨r2,g2,h⟩ := bind_success _ _ _ h
        cases r2 with
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
          cases h
        | Ok u2 =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
          obtain ⟨r3,g3,h⟩ := bind_success _ _ _ h
          cases r3 with
          | Err error =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
            cases h
          | Ok u3 =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
            obtain ⟨r4,g4,h⟩ := bind_success _ _ _ h
            cases r4 with
            | Err error =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
              cases h
            | Ok u4 =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
              cases u0; cases u1; cases u2; cases u3; cases u4
              exact ⟨master,forest,selected,checkpoint,im,ic,il,iv,g1,g2,g3,g4⟩
  · rw [if_neg size] at accepted
    dsimp only at accepted
    split at accepted <;> cases accepted

#print axioms guards
end AspisR1.Hist_Asq8Guards
end
