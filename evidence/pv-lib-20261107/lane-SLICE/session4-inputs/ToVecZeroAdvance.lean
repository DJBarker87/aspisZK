import PV_STX2_ToVecZeroHeaderAction
set_option autoImplicit false
noncomputable section
namespace PV_STX2_ToVecZeroAdvance
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OWNER
/-- Conditional on owner acceptance of the translator patch. One corrected
source transition, retaining terminal stuttering and the exact event suffix. -/
def next (resources : Resources) (encode : Encode) (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (p : PV_STX2_SliceMachine.Prefix OWNER PV_RJ4IDB.NativeEvent) :
    PV_STX2_SliceMachine.Prefix OWNER PV_RJ4IDB.NativeEvent :=
  match p.status with
  | .running c =>
      let q := PV_STX2_ToVecZeroHeaderAction.step resources encode C K P H c p.world
      ⟨q.status,q.world,p.events ++ q.events⟩
  | _ => p
/-- Conditional on owner acceptance of the translator patch. Iterate the
same corrected machine from its original entry, without replacing any world. -/
def advance (resources : Resources) (encode : Encode) (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data) :
    Nat → PV_STX2_SliceMachine.Prefix OWNER PV_RJ4IDB.NativeEvent →
      PV_STX2_SliceMachine.Prefix OWNER PV_RJ4IDB.NativeEvent
  | 0,p => p
  | n+1,p => next resources encode C K P H (advance resources encode C K P H n p)
/-- Conditional on owner acceptance of the translator patch. Generic
trace-indexed prefix identity before the single new zero action. It uses only
the configurations actually reached by the existing run; no global reachable
invariant, store normalization, new reply or site-by-site simulation is needed.
The source74 application must discharge avoids from its emitted trace. -/
theorem prefix_identity (resources : Resources) (encode : Encode) (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (n : Nat) (p : PV_STX2_SliceMachine.Prefix OWNER PV_RJ4IDB.NativeEvent) :
    (∀ i, i<n → ∀ c,
      (PV_STX2_Source7IterationBindings.advance resources encode C K P H i p).status = .running c →
      PV_STX2_ToVecZeroHeaderAction.zeroSite c = false) →
    advance resources encode C K P H n p =
      PV_STX2_Source7IterationBindings.advance resources encode C K P H n p := by
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro avoids
    have pre := ih (fun i hi c hc => avoids i (Nat.lt_trans hi (Nat.lt_succ_self n)) c hc)
    rw [advance,pre,PV_STX2_Source7IterationBindings.advance_add resources encode C K P H n 1 p]
    generalize hq : PV_STX2_Source7IterationBindings.advance resources encode C K P H n p = q
    cases hs : q.status with
    | running c =>
      have other := avoids n (Nat.lt_succ_self n) c (by rw [hq]; exact hs)
      simp only [next,hs,PV_STX2_Source7IterationBindings.advance,
        PV_STX2_ToVecZeroHeaderAction.unchanged resources encode C K P H c q.world other]
    | returned r s => simp only [next,hs,PV_STX2_Source7IterationBindings.advance]
    | fault f s => simp only [next,hs,PV_STX2_Source7IterationBindings.advance]
    | undefined site s => simp only [next,hs,PV_STX2_Source7IterationBindings.advance]
#print axioms next
#print axioms advance
#print axioms prefix_identity
end PV_STX2_ToVecZeroAdvance
