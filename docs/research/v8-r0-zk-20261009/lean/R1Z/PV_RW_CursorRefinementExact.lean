import R1Z.PV_RW_CursorRefinement
set_option autoImplicit false
namespace R1Z.PV_RW_CursorRefinementExact
open PV_RW_Cursor PV_RW_Outcome

-- Unlike the earlier sufficiency-based transport, this preserves every fuel,
-- including exhausted budgets, without assuming a bound on the input length.
theorem bounded {E T U S V : Type} (value : T → U) (state : S → V)
    (left : T → S → Outcome E S) (right : U → V → Outcome E V)
    (same : ∀ item acc, PV_RW_Outcome.map id state (left item acc)=right (value item) (state acc))
    (fuel : Nat) (cursor : Cursor T) (acc : S) :
    PV_RW_Outcome.map id state (PV_RW_CursorLoop.bounded left fuel cursor acc)=
      PV_RW_CursorLoop.bounded right fuel (PV_RW_CursorMap.map value cursor) (state acc) := by
  induction fuel generalizing cursor acc with
  | zero => rfl
  | succ fuel ih =>
    rw [PV_RW_CursorLoop.bounded,PV_RW_CursorLoop.bounded,PV_RW_CursorMap.next]
    cases h : PV_RW_Cursor.next cursor with
    | mk head next =>
      cases head with
      | none => rfl
      | some item =>
        change PV_RW_Outcome.map id state (PV_RW_Outcome.bind (left item acc)
          (PV_RW_CursorLoop.bounded left fuel next))=
          PV_RW_Outcome.bind (right (value item) (state acc))
            (PV_RW_CursorLoop.bounded right fuel (PV_RW_CursorMap.map value next))
        rw [← same item acc]
        apply PV_RW_CursorRefinement.bind_refines
        intro nextAcc
        exact ih next nextAcc
#print axioms bounded
end R1Z.PV_RW_CursorRefinementExact
