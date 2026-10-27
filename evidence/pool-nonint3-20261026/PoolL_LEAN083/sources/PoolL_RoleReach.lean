import PoolL_CanonicalRoleAccepted
import PoolL_FreshRoleControl
import PoolL_FreshReach
import PoolL_MarkerRoleControl
import PoolL_MarkerReach
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_RoleReach
open Aeneas Aeneas.Std Result
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
local instance : DecidableEq Key := Classical.decEq _
def zeroState : Slice U8 := ⟨List.replicate 1000 (0#u8),by simp only [List.length_replicate]; scalar_tac⟩

theorem canonical (a : Account) (id : Key) :
    PoolL_CanonicalRoleSource.PoolL_canonical_role
      {a with owner := id, executable := false, is_signer := false, is_writable := true}
      id (.Ok zeroState) = ok (.Ok ()) := by
  apply (PoolL_CanonicalRoleAccepted.accepted _ _ _).mpr
  refine ⟨rfl,rfl,rfl,rfl,zeroState,rfl,?_⟩
  exact List.length_replicate
/-- System-empty source branch accepts independently of an unreached borrow error.
No account with occupied checkpoint bytes is asserted to have this metadata. -/
theorem fresh (a : Account) (id expected system : Key) (different : system ≠ id)
    (err : AdapterRw.solana_program_error.ProgramError) (size : Usize) :
    PoolL_FreshRoleSource.PoolL_fresh_role
      {a with key := expected, owner := system, executable := false, is_signer := false, is_writable := true}
      id expected system true (.Err err) size = ok (.Ok ()) := by
  rw [PoolL_FreshRoleControl.control]
  have h := PoolL_FreshReach.reachable {a with owner := system} expected
  dsimp at h
  rw [h]
  simp only [PoolM_NativeCancelGuard.thenResult]
  change (if system = id then (ok (core.result.Result.Err err) : Result (core.result.Result Unit AdapterRw.solana_program_error.ProgramError)) else if system = system ∧ true = true then ok (core.result.Result.Ok ()) else _) = _
  rw [if_neg different,if_pos ⟨rfl,rfl⟩]
theorem marker (a : Account) (id system : Key) (different : system ≠ id)
    (err : AdapterRw.solana_program_error.ProgramError) :
    PoolL_MarkerRoleSource.PoolL_marker_role
      {a with owner := system, executable := false, is_signer := false, is_writable := true}
      id system true (.Err err) = ok (.Ok ()) := by
  rw [PoolL_MarkerRoleControl.control]
  have h := PoolL_MarkerReach.reachable {a with owner := system}
  dsimp at h
  rw [h]
  simp only [PoolM_NativeCancelGuard.thenResult]
  change (if system = id then (ok (core.result.Result.Err err) : Result (core.result.Result Unit AdapterRw.solana_program_error.ProgramError)) else if system = system ∧ true = true then ok (core.result.Result.Ok ()) else _) = _
  rw [if_neg different,if_pos ⟨rfl,rfl⟩]
#print axioms canonical
#print axioms fresh
#print axioms marker
end AspisR1.PoolL_RoleReach
end
