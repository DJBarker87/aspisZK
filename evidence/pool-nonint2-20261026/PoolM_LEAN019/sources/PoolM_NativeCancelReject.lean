import PoolM_NativeCancelGuard
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolM_NativeCancelReject
open Aeneas Aeneas.Std Result
open PoolM_NativeCancelGuard PoolM_NativeCancelSource
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev Error := AdapterRw.solana_program_error.ProgramError

theorem then_accepted (check next : Result (core.result.Result Unit Error)) :
    thenResult check next = ok (.Ok ()) ↔ check = ok (.Ok ()) ∧ next = ok (.Ok ()) := by
  cases check with
  | ok r => cases r with
    | Ok u => cases u; simp [thenResult]
    | Err e => simp [thenResult]
  | fail e => simp [thenResult]
  | div => simp [thenResult]

/-- Acceptance of the actual extracted role cut forces the exact reached
length Results; failure/divergence and earlier ProgramErrors cannot accept. -/
theorem accepted (readLength : Account → Result Usize) (system id : Key)
    (payer coreAcc shard : Account) (hasShard : Bool) :
    PoolM_cancel_roles_native readLength system id payer coreAcc shard hasShard = ok (.Ok ()) ↔
    payer.is_signer = true ∧ payer.is_writable = true ∧ payer.executable = false ∧
      payer.owner = system ∧
      require_prepared_plan_account_v1 readLength coreAcc id 10000#usize = ok (.Ok ()) ∧
      (hasShard = true →
        require_prepared_plan_account_v1 readLength shard id 8504#usize = ok (.Ok ())) := by
  classical
  rw [native_control]
  by_cases owner : payer.owner = system <;>
    cases hs : payer.is_signer <;> cases hw : payer.is_writable <;>
    cases he : payer.executable <;> cases hasShard <;>
    simp [hs,hw,he,owner,PoolM_NativePlanGuard.key_ne,suffix,then_accepted]

theorem lengths (readLength : Account → Result Usize) (system id : Key)
    (payer coreAcc shard : Account) (hasShard : Bool)
    (yes : PoolM_cancel_roles_native readLength system id payer coreAcc shard hasShard = ok (.Ok ())) :
    readLength coreAcc = ok 10000#usize ∧
      (hasShard = true → readLength shard = ok 8504#usize) := by
  obtain ⟨_,_,_,_,hc,hh⟩ := (accepted readLength system id payer coreAcc shard hasShard).mp yes
  rw [prepared_eq] at hc
  have coreLen := ((PoolM_NativePlanGuard.accepted coreAcc id 10000#usize (readLength coreAcc)).mp hc).2.2.2.2
  constructor
  · exact coreLen
  · intro live
    have shardOk := hh live
    rw [prepared_eq] at shardOk
    exact ((PoolM_NativePlanGuard.accepted shard id 8504#usize (readLength shard)).mp shardOk).2.2.2.2

/-- There is no accepted path when the occupied checkpoint fills the core
role, including arbitrary errors/effects of the unexecuted later shard. -/
theorem core_occupied (readLength : Account → Result Usize) (system id : Key)
    (payer coreAcc shard : Account) (hasShard : Bool) (n : Usize)
    (cp : n.val = 192 ∨ n.val = 1768) (actual : readLength coreAcc = ok n) :
    PoolM_cancel_roles_native readLength system id payer coreAcc shard hasShard ≠ ok (.Ok ()) := by
  intro yes
  have len := (lengths readLength system id payer coreAcc shard hasShard yes).1
  rw [actual] at len
  have eq := Result.ok.inj len
  rcases cp with cp | cp <;> scalar_tac

theorem shard_occupied (readLength : Account → Result Usize) (system id : Key)
    (payer coreAcc shard : Account) (n : Usize)
    (cp : n.val = 192 ∨ n.val = 1768) (actual : readLength shard = ok n) :
    PoolM_cancel_roles_native readLength system id payer coreAcc shard true ≠ ok (.Ok ()) := by
  intro yes
  have len := (lengths readLength system id payer coreAcc shard true yes).2 rfl
  rw [actual] at len
  have eq := Result.ok.inj len
  rcases cp with cp | cp <;> scalar_tac

/-- Occupied Pool/verifier-owned accounts fail the authority System-owner test.
The actual owner inequality must come from the same runtime account. -/
theorem authority_occupied (readLength : Account → Result Usize) (system id : Key)
    (payer coreAcc shard : Account) (hasShard : Bool) (notSystem : payer.owner ≠ system) :
    PoolM_cancel_roles_native readLength system id payer coreAcc shard hasShard ≠ ok (.Ok ()) := by
  intro yes
  exact notSystem ((accepted readLength system id payer coreAcc shard hasShard).mp yes).2.2.2.1

#print axioms then_accepted
#print axioms accepted
#print axioms lengths
#print axioms core_occupied
#print axioms shard_occupied
#print axioms authority_occupied
end AspisR1.PoolM_NativeCancelReject
end
