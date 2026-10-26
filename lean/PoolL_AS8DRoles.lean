import PoolL_RoleComposition
import PoolL_Physical
set_option autoImplicit false
namespace AspisR1.PoolL_AS8DRoles
open Aeneas Aeneas.Std Result PoolL_Physical
open PoolM_NativeCancelEffects (Outcome afterGuard)
/-- F:988-1190 lane/page decoder cuts after actual earlier arithmetic/address results.
Local role cut with complete supplied prior state/log. This is NOT the
whole-handler frame: source account selection and execution instance remain. -/
theorem role_frame {S E V : Type} (s : Snapshot) (key id system expected : Key) (refund : Account) (size : Usize)
    (cp : Occupied s key)
    (shape : size.val = 768 ∨ size.val = 8256)
    (before : Result (core.result.Result Unit AdapterRw.solana_program_error.ProgramError))
    (state : S) (prior : List E) (next : S → List E → Outcome S E V) :
    (afterGuard (PoolM_NativeCancelGuard.thenResult before (PoolL_LengthSource.lengthPrefix (bytes s key) size)) state prior next).state = state ∧
    (afterGuard (PoolM_NativeCancelGuard.thenResult before (PoolL_LengthSource.lengthPrefix (bytes s key) size)) state prior next).effects = prior := by
  have other : PoolL_LengthOccupied.OtherWidth size.val := by
    rcases shape with h | h <;> simp [PoolL_LengthOccupied.OtherWidth,h]
  have err := PoolL_LengthOccupied.rejects (bytes s key) size cp other
  apply PoolL_RoleComposition.blocked
  rw [err]
  intro bad
  cases bad
#print axioms role_frame
end AspisR1.PoolL_AS8DRoles
