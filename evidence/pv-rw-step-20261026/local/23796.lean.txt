import R1Z.PV_RW_NativeForModel
import R1Z.PV_RW_CursorRefinementExact
set_option autoImplicit false
namespace R1Z.PV_RW_NativeForRefinement
open Aeneas Aeneas.Std Result
open PV_RW_NativeForSource

theorem bounded {S V : Type} (state : S → V) (left : U32 → S → Result S)
    (right : U32 → V → Result V)
    (same : ∀ value acc, PV_RW_Outcome.map id state (PV_RW_ResultOutcome.toOutcome (left value acc))=
      PV_RW_ResultOutcome.toOutcome (right value (state acc)))
    (fuel : Nat) (iterator : Iter) (acc : S) :
    PV_RW_Outcome.map id state
      (PV_RW_ResultOutcome.toOutcome (PV_RW_NativeForSource.bounded left fuel iterator acc))=
      PV_RW_ResultOutcome.toOutcome (PV_RW_NativeForSource.bounded right fuel iterator (state acc)) := by
  rw [PV_RW_NativeForModel.bounded,PV_RW_NativeForModel.bounded]
  have eq := PV_RW_CursorRefinementExact.bounded id state
    (fun value acc => PV_RW_ResultOutcome.toOutcome (left value acc))
    (fun value acc => PV_RW_ResultOutcome.toOutcome (right value acc)) same fuel
    (PV_RW_NativeCursor.cursor iterator) acc
  simpa only [PV_RW_CursorMap.map,List.map_id] using eq

theorem run {S V : Type} (state : S → V) (left : U32 → S → Result S)
    (right : U32 → V → Result V)
    (same : ∀ value acc, PV_RW_Outcome.map id state (PV_RW_ResultOutcome.toOutcome (left value acc))=
      PV_RW_ResultOutcome.toOutcome (right value (state acc)))
    (iterator : Iter) (acc : S) :
    PV_RW_Outcome.map id state
      (PV_RW_ResultOutcome.toOutcome (PV_RW_NativeForSource.run left iterator acc))=
      PV_RW_ResultOutcome.toOutcome (PV_RW_NativeForSource.run right iterator (state acc)) := by
  rw [PV_RW_NativeForModel.run,PV_RW_NativeForModel.run]
  have eq := PV_RW_CursorRefinement.list_refines id state
    (fun value acc => PV_RW_ResultOutcome.toOutcome (left value acc))
    (fun value acc => PV_RW_ResultOutcome.toOutcome (right value acc)) same
    (PV_RW_Cursor.remaining (PV_RW_NativeCursor.cursor iterator)) acc
  simpa only [List.map_id] using eq
#print axioms bounded
#print axioms run
end R1Z.PV_RW_NativeForRefinement
