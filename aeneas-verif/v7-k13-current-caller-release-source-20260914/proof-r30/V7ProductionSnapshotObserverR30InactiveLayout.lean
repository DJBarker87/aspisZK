import V7ProductionSnapshotObserverR28.Funs
import V7CallerCurrentReleaseR26GroupedRows

/-!
# Concrete inactive grouped-layout copies used by the production observer

The production external bindings contain the complete fixed row-group and
mask literals.  These lemmas identify their successful outputs with the
released vectors consumed by the terminal grouped-fold proof.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7ProductionSnapshotObserverR28
open V7CallerCurrentReleaseR26

namespace V7ProductionSnapshotObserverR30InactiveLayout

open V7CallerCurrentReleaseR26GroupedFold
open V7CallerCurrentReleaseR26GroupedRows

theorem inactive_row_groups_copy_exact
    (out : Array Std.U8 64#usize)
    (run :
      aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_row_groups_v3 =
        ok out) :
    out.val = releasedRowGroups64.val := by
  unfold aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_row_groups_v3
    at run
  simp only [Result.ok.injEq] at run
  subst out
  rfl

theorem inactive_group_masks_copy_exact
    (out : Slice Std.U16)
    (run :
      aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_group_masks_v3 =
        ok out) :
    out.val = releasedMasks.val := by
  unfold aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_group_masks_v3
    at run
  simp only [Result.ok.injEq] at run
  subst out
  rfl

#print axioms inactive_row_groups_copy_exact
#print axioms inactive_group_masks_copy_exact

end V7ProductionSnapshotObserverR30InactiveLayout
