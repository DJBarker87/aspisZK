import PoolL_RoleComposition
import PoolL_PhysicalClose
set_option autoImplicit false
namespace AspisR1.PoolL_ASPFRoles
open Aeneas Aeneas.Std Result PoolL_Physical
open PoolM_NativeCancelEffects (Outcome afterGuard)
/-- P:1674-1910 final core/shard close guard cuts.
Local role cut with complete supplied prior state/log. This is NOT the
whole-handler frame: source account selection and execution instance remain. -/
theorem role_frame {S E V : Type} (s : Snapshot) (key id system expected : Key) (refund : Account) (size : Usize)
    (cp : Occupied s key)
    (shape : size.val = 10000 ∨ size.val = 8504)
    (before : Result (core.result.Result Unit AdapterRw.solana_program_error.ProgramError))
    (state : S) (prior : List E) (next : S → List E → Outcome S E V) :
    (afterGuard (PoolM_NativeCancelGuard.thenResult before (PoolL_CloseSource.closePrefix (readLength s) (observe s key) refund id size)) state prior next).state = state ∧
    (afterGuard (PoolM_NativeCancelGuard.thenResult before (PoolL_CloseSource.closePrefix (readLength s) (observe s key) refund id size)) state prior next).effects = prior := by
  have err := PoolL_PhysicalClose.excluded s key id refund size cp shape
  apply PoolL_RoleComposition.blocked
  rw [err]
  intro bad
  cases bad
#print axioms role_frame
end AspisR1.PoolL_ASPFRoles
