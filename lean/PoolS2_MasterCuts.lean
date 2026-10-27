import PoolS2_MasterRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_MasterCuts
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_MasterRead

/-- ONE owned reference invocation supplies its own actual raw read, decoder
return, PDA check and self-key join. This is not native master/Box refinement. -/
theorem accepted (decode : Decode) (pda : Ops) (program : Key) (account : Account)
    (writable : Bool) (master : Master)
    (h : run decode pda program account writable = ok (.Ok master)) :
    Hiq_PoolSource.history.require_program_account account program writable = ok (.Ok ()) ∧
    account.is_signer = false ∧
    ∃ bytes : alloc.vec.Vec U8,
      account.bytes = .Ok bytes ∧ decode bytes.deref = ok (.Ok master) ∧
      pair_forest.master_address_matches pda program master account.key = ok true ∧
      master.identity.pool = account.key := by
  classical
  unfold run at h
  repeat' first
  | (solve | cases h)
  | uncase_result
  | head_reduce h
  | split at h
  all_goals aesop

#print axioms accepted
end AspisR1.PoolS2_MasterCuts
end
