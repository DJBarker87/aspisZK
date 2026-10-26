import PoolL_RoleComposition
import PoolL_PhysicalFresh
set_option autoImplicit false
namespace AspisR1.PoolL_ASPPRoles
open Aeneas Aeneas.Std Result PoolL_Physical
open PoolM_NativeCancelEffects (Outcome afterGuard)
/-- P:1167-1363 core/shard freshness after plan construction and optional earlier CPI.
Local role cut with complete supplied prior state/log. This is NOT the
whole-handler frame: source account selection and execution instance remain. -/
theorem role_frame {S E V : Type} (s : Snapshot) (key id system expected : Key) (refund : Account) (size : Usize)
    (cp : Occupied s key)
    (shape : size.val = 10000 ∨ size.val = 8504)
    (before : Result (core.result.Result Unit AdapterRw.solana_program_error.ProgramError))
    (state : S) (prior : List E) (next : S → List E → Outcome S E V) :
    (afterGuard (PoolM_NativeCancelGuard.thenResult before (PoolL_FreshRoleSource.PoolL_fresh_role (observe s key) id expected system
      (decide ((bytes s key).val.length = 0)) (.Ok (bytes s key)) size)) state prior next).state = state ∧
    (afterGuard (PoolM_NativeCancelGuard.thenResult before (PoolL_FreshRoleSource.PoolL_fresh_role (observe s key) id expected system
      (decide ((bytes s key).val.length = 0)) (.Ok (bytes s key)) size)) state prior next).effects = prior := by
  have other : PoolL_LengthOccupied.OtherWidth size.val := by
    rcases shape with h | h <;> simp [PoolL_LengthOccupied.OtherWidth,h]
  have err := PoolL_PhysicalFresh.excluded s key id expected system size cp other
  apply PoolL_RoleComposition.blocked
  rw [err]
  intro bad
  cases bad
#print axioms role_frame
end AspisR1.PoolL_ASPPRoles
