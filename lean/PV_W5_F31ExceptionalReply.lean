import PV_W5_F31Replies
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace PV_W5_F31ExceptionalReply
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER
open PV_STX2_SliceMachine PV_STX2_Source7ConstructorEntry

/-- The exceptional full reply retains the exact source-issued store. -/
theorem store (D : Carrier OWNER Data) (s : Store Data) (parent : Frame)
    (parents : List Frame) (a : Nat) (length alloc layout : Data)
    (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) (prior : List PV_RJ4IDB.NativeEvent)
    (exceptional : ∀ value, r.answer ≠ .returned (.ok value)) :
    PV_W5_LeafBoundary.statusStore
      (PV_W5_F31Replies.received D s (parent::parents) a length alloc layout r prior).status =
      entered s a length alloc layout := by
  rcases r with ⟨answer,post,events⟩
  cases answer with
  | pending => rfl
  | fault f => cases f <;> rfl
  | returned result =>
    cases result with
    | ok v => exact False.elim (exceptional v rfl)
    | fail e => rfl
    | div => rfl

theorem world_events (D : Carrier OWNER Data) (s : Store Data) (parents : List Frame)
    (a : Nat) (length alloc layout : Data) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (prior : List PV_RJ4IDB.NativeEvent) :
    (PV_W5_F31Replies.received D s parents a length alloc layout r prior).world=r.world ∧
    (PV_W5_F31Replies.received D s parents a length alloc layout r prior).events=prior++r.events := by
  rcases r with ⟨answer,post,events⟩
  cases answer with
  | pending => exact ⟨rfl,rfl⟩
  | fault f => cases f <;> exact ⟨rfl,rfl⟩
  | returned result => cases result <;> cases parents <;> exact ⟨rfl,rfl⟩

theorem entered_frame (s : Store Data) (a : Nat) (length alloc layout : Data) :
    PV_W5_F59Frame.StoreFrame s (entered s a length alloc layout) a := by
  constructor
  · simp only [entered,PV_W5_LeafBoundary.arguments_counter]
    exact Nat.le_succ _
  · intro p outside older
    rw [entered,PV_W5_LeafBoundary.arguments_frame _ _ _ _ p (by omega)]
    rcases p with ⟨pa,pi,pp⟩
    change pa ≠ a at outside
    simp [prepared,write, outside]

#print axioms store
#print axioms world_events
#print axioms entered_frame
end PV_W5_F31ExceptionalReply
