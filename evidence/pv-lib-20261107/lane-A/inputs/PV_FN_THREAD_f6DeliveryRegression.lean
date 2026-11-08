import PV_FN_THREAD_f6DeliveryBoundary
import PV_FN_THREAD_f6DivergenceBeforeReturn
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6DeliveryRegression
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f6Interfaces PV_FN_THREAD_f6DivergenceBoundary
open PV_FN_THREAD_f6Joins

/-- The checked D933 divergence is delivered to the immediate caller at19,
with its exact status, store, world, events and suspended suffix. -/
theorem delivered19 {E : Type} (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (x : Entry E) (body : x.body = PV_THR2_F6.live) (valid : EntryValid x)
    (lower : x.parents ≠ []) (diverged : (reply x H).answer = .returned .div) :
    Delivered x (run (machine C b K P H) x 19) := by
  rw [PV_FN_THREAD_f6DivergenceBeforeReturn.run19 C b K P H x body valid lower diverged]
  exact Or.inr (Or.inl ⟨_,.div,rfl,rfl,rfl,rfl⟩)

/-- The lower-frame gap at20 is outside the repaired boundary, without any
extra lower-stack validity or restriction to successful replies. -/
theorem excludes20 {E : Type} (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (x : Entry E) (body : x.body = PV_THR2_F6.live) (valid : EntryValid x)
    (lower : x.parents ≠ []) (diverged : (reply x H).answer = .returned .div) :
    ¬ BeforeDelivery (machine C b K P H) x 20 := by
  exact delivery_stops _ x 19 (delivered19 C b K P H x body valid lower diverged)

/-- Success restoration remains an outcome delivery; the boundary repair does
not discard any old success endpoint. -/
theorem returned_delivered {E : Type} (x : Entry E)
    (q : PV_THR2_IntrinsicState.State OWNER E) (returned : Returned x q) :
    Delivered x q := Or.inl returned

/-- Every repaired prefix is an old pre-restoration prefix. Existing local
prefix facts can therefore be restricted without executing a caller suffix. -/
theorem before_return {E : Type} (M : Machine E) (x : Entry E) (n : Nat)
    (before : BeforeDelivery M x n) : BeforeReturn M x n := by
  intro k hk returned
  exact before k hk (Or.inl (Or.inl returned))

/-- The historical FullPost implies the corrected boundary for the SAME value
predicate. This is a restriction theorem, not an assertion of either contract. -/
theorem restrict_full_post {E : Type} (M : Machine E) (x : Entry E)
    (valuePost : Store Data → OWNER → Data → Prop)
    (old : PV_FN_THREAD_f6Interfaces.FullPost M x valuePost) :
    PV_FN_THREAD_f6Joins.FullPost M x valuePost := by
  intro n before
  exact old n (before_return M x n before)

#print axioms delivered19
#print axioms excludes20
#print axioms returned_delivered
#print axioms before_return
#print axioms restrict_full_post
end PV_FN_THREAD_f6DeliveryRegression
