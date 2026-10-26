import PoolL_RoleComposition
import PoolL_PhysicalMarker
set_option autoImplicit false
namespace AspisR1.PoolL_ASQ8Roles
open Aeneas Aeneas.Std Result PoolL_Physical
open PoolM_NativeCancelEffects (Outcome afterGuard)
/-- F:1615-1820 marker classification cut; readonly ASC8/CP and other role/CPI joins remain.
Local role cut with complete supplied prior state/log. This is NOT the
whole-handler frame: source account selection and execution instance remain. -/
theorem role_frame {S E V : Type} (s : Snapshot) (key id system expected : Key) (refund : Account)
    (cp : Occupied s key)
    (before : Result (core.result.Result Unit AdapterRw.solana_program_error.ProgramError))
    (state : S) (prior : List E) (next : S → List E → Outcome S E V) :
    (afterGuard (PoolM_NativeCancelGuard.thenResult before (PoolL_MarkerRoleSource.PoolL_marker_role (observe s key) id system
      (decide ((bytes s key).val.length = 0)) (.Ok (bytes s key)))) state prior next).state = state ∧
    (afterGuard (PoolM_NativeCancelGuard.thenResult before (PoolL_MarkerRoleSource.PoolL_marker_role (observe s key) id system
      (decide ((bytes s key).val.length = 0)) (.Ok (bytes s key)))) state prior next).effects = prior := by
  have err := PoolL_PhysicalMarker.excluded s key id system cp
  apply PoolL_RoleComposition.blocked
  rw [err]
  intro bad
  cases bad
#print axioms role_frame
end AspisR1.PoolL_ASQ8Roles
