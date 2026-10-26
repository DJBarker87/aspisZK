import R1Z.PV_RW_CursorLoop
import R1Z.PV_RW_CursorMap
set_option autoImplicit false
namespace R1Z.PV_RW_CursorRefinement
open PV_RW_Cursor PV_RW_Outcome

-- Error tags are unchanged, and divergence is preserved exactly.
theorem bind_refines {E A B C D : Type} (before : A → B) (after : C → D)
    (result : Outcome E A) (left : A → Outcome E C) (right : B → Outcome E D)
    (same : ∀ a, PV_RW_Outcome.map id after (left a)=right (before a)) :
    PV_RW_Outcome.map id after (bind result left)=
      bind (PV_RW_Outcome.map id before result) right := by
  cases result with
  | ok a => exact same a
  | fail error => rfl
  | div => rfl

theorem list_refines {E T U S V : Type} (value : T → U) (state : S → V)
    (left : T → S → Outcome E S) (right : U → V → Outcome E V)
    (same : ∀ item acc, PV_RW_Outcome.map id state (left item acc)=right (value item) (state acc))
    (values : List T) (acc : S) :
    PV_RW_Outcome.map id state (PV_RW_CursorLoop.listRun left values acc)=
      PV_RW_CursorLoop.listRun right (values.map value) (state acc) := by
  induction values generalizing acc with
  | nil => rfl
  | cons item items ih =>
    simp only [PV_RW_CursorLoop.listRun,List.map_cons]
    rw [← same item acc]
    apply bind_refines
    intro next
    exact ih next

theorem bounded_refines {E T U S V : Type} (value : T → U) (state : S → V)
    (left : T → S → Outcome E S) (right : U → V → Outcome E V)
    (same : ∀ item acc, PV_RW_Outcome.map id state (left item acc)=right (value item) (state acc))
    (fuel : Nat) (cursor : Cursor T) (acc : S) (bound : (remaining cursor).length<fuel) :
    PV_RW_Outcome.map id state (PV_RW_CursorLoop.bounded left fuel cursor acc)=
      PV_RW_CursorLoop.bounded right fuel (PV_RW_CursorMap.map value cursor) (state acc) := by
  rw [PV_RW_CursorLoop.complete left fuel cursor acc bound]
  rw [PV_RW_CursorLoop.complete right fuel (PV_RW_CursorMap.map value cursor) (state acc)
    (by rw [PV_RW_CursorMap.remaining_length]; exact bound)]
  rw [PV_RW_CursorMap.remaining]
  exact list_refines value state left right same (remaining cursor) acc
#print axioms bind_refines
#print axioms list_refines
#print axioms bounded_refines
end R1Z.PV_RW_CursorRefinement
