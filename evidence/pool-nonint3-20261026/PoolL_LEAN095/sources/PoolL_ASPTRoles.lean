import PoolL_RoleComposition
import PoolL_PhysicalCanonical
set_option autoImplicit false
namespace AspisR1.PoolL_ASPTRoles
open Aeneas Aeneas.Std Result PoolL_Physical
open PoolM_NativeCancelEffects (Outcome afterGuard)
/-- P:2024-2187 primary canonical-state cut.
Local role cut with complete supplied prior state/log. This is NOT the
whole-handler frame: source account selection and execution instance remain. -/
theorem role_frame {S E V : Type} (s : Snapshot) (key id system expected : Key) (refund : Account)
    (cp : Occupied s key)
    (before : Result (core.result.Result Unit AdapterRw.solana_program_error.ProgramError))
    (state : S) (prior : List E) (next : S → List E → Outcome S E V) :
    (afterGuard (PoolM_NativeCancelGuard.thenResult before (PoolL_CanonicalRoleSource.PoolL_canonical_role (observe s key) id (.Ok (bytes s key)))) state prior next).state = state ∧
    (afterGuard (PoolM_NativeCancelGuard.thenResult before (PoolL_CanonicalRoleSource.PoolL_canonical_role (observe s key) id (.Ok (bytes s key)))) state prior next).effects = prior := by
  exact PoolL_RoleComposition.blocked before _ (PoolL_PhysicalCanonical.excluded s key id cp) state prior next
#print axioms role_frame
end AspisR1.PoolL_ASPTRoles
