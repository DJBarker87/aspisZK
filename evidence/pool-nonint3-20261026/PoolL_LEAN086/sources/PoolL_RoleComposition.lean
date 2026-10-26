import PoolM_NativeCancelEffects
import PoolM_NativeCancelReject
set_option autoImplicit false
namespace AspisR1.PoolL_RoleComposition
open Aeneas Aeneas.Std Result
open PoolM_NativeCancelEffects (Outcome afterGuard blocked_frame)
abbrev Error := AdapterRw.solana_program_error.ProgramError
/-- Compose a prior child Result with the blocked role guard. Supplied state
and ordered log are the actual pre-cut observations, not an empty prefix.
This lemma does not derive those observations from an enclosing handler. -/
theorem blocked {S E V : Type} (before guard : Result (core.result.Result Unit Error))
    (no : guard ≠ ok (.Ok ())) (state : S) (prior : List E)
    (next : S → List E → Outcome S E V) :
    (afterGuard (PoolM_NativeCancelGuard.thenResult before guard) state prior next).state = state ∧
    (afterGuard (PoolM_NativeCancelGuard.thenResult before guard) state prior next).effects = prior := by
  apply blocked_frame
  intro yes
  exact no ((PoolM_NativeCancelReject.then_accepted before guard).mp yes).2

theorem rejected_result (before guard : Result (core.result.Result Unit Error))
    (no : guard ≠ ok (.Ok ())) :
    PoolM_NativeCancelGuard.thenResult before guard ≠ ok (.Ok ()) := by
  intro yes
  exact no ((PoolM_NativeCancelReject.then_accepted before guard).mp yes).2
#print axioms blocked
#print axioms rejected_result
end AspisR1.PoolL_RoleComposition
