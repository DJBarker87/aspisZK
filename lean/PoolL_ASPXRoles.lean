import PoolL_CancelPhysical
import PoolL_RoleComposition
set_option autoImplicit false
namespace AspisR1.PoolL_ASPXRoles
open Aeneas Aeneas.Std Result PoolL_Physical
open PoolM_NativeCancelEffects (Outcome afterGuard)
/-- Native ASPX role cut across all three physical alias positions. Complete
parser/unique selection and whole-handler suffix instance remain open. -/
theorem role_frame {S E V : Type} (s : Snapshot) (target payer coreKey shardKey system id : Key)
    (hasShard : Bool) (cp : Occupied s target) (notSystem : (observe s target).owner ≠ system)
    (appears : target = payer ∨ target = coreKey ∨ (hasShard = true ∧ target = shardKey))
    (before : Result (core.result.Result Unit AdapterRw.solana_program_error.ProgramError))
    (state : S) (prior : List E) (next : S → List E → Outcome S E V) :
    (afterGuard (PoolM_NativeCancelGuard.thenResult before
      (PoolM_NativeCancelSource.PoolM_cancel_roles_native (readLength s) system id
      (observe s payer) (observe s coreKey) (observe s shardKey) hasShard)) state prior next).state = state ∧
    (afterGuard (PoolM_NativeCancelGuard.thenResult before
      (PoolM_NativeCancelSource.PoolM_cancel_roles_native (readLength s) system id
      (observe s payer) (observe s coreKey) (observe s shardKey) hasShard)) state prior next).effects = prior := by
  apply PoolL_RoleComposition.blocked
  intro accepted
  have sep := PoolL_CancelPhysical.accepted_separation s target payer coreKey shardKey system id hasShard cp notSystem accepted
  rcases appears with h | h | ⟨live,h⟩
  · exact sep.1 h
  · exact sep.2.1 h
  · exact sep.2.2 live h
#print axioms role_frame
end AspisR1.PoolL_ASPXRoles
