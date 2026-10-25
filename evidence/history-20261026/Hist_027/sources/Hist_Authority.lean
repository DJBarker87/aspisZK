import S2W_EntryPrivileges
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_Authority
open Aeneas Aeneas.Std Result
abbrev Key := AdapterRw.solana_pubkey.Pubkey

/-- Pure public-key equality is the documented std/library interpretation,
not an oracle, syscall or success hypothesis about the surrounding caller. -/
def keyEq (left right : Key) : Result Bool := ok (decide (left = right))
def install (base : AdapterRw.Ops) : AdapterRw.Ops := {base with op36 := keyEq}

theorem keyEq_true (left right : Key) (accepted : keyEq left right = ok true) : left = right := by
  have h : decide (left = right) = true := Result.ok.inj accepted
  exact of_decide_eq_true h

theorem checkpoint_owner (base : AdapterRw.Ops) (account : AdapterRw.Cuts.Account)
    (program : Key) (writable : Bool)
    (accepted : AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint (install base)
      account program writable = ok (.Ok ())) : account.owner = program := by
  unfold AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.owner
    AdapterRw.core.cmp.impls.PartialEqShared.ne
    AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey
    AdapterRw.core.cmp.PartialEq.ne.trait_default install keyEq at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals aesop

theorem accepted_owner (base : AdapterRw.Ops) (program : Key)
    (accounts : Slice AdapterRw.Cuts.Account) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned (install base) program accounts data = ok (.Ok saved)) :
    ∃ account, Slice.index_usize accounts 2#usize = ok account ∧ account.owner = program := by
  obtain ⟨pa,pu,ca,_,_,index,_,_,guard⟩ := S2W_EntryPrivileges.guards (install base) program accounts data saved accepted
  exact ⟨ca,index,checkpoint_owner base ca program true guard⟩

#print axioms keyEq_true
#print axioms checkpoint_owner
#print axioms accepted_owner
end AspisR1.Hist_Authority
end
