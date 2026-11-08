import PV_LIB_SPEC_NativePoll20
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_LocalReturn20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen

/-- Exact generic native return administration: child result and local
destination are both retained, as are the full store counter and callers. -/
theorem delivered (base : Carrier OWNER Data) (s : Store Data) (a child dest : Nat)
    (body : List PV_STX2_SliceSyntax.Node) (parents : List Frame)
    (req : PV_STX2_Native.Request Data) (value : Data) (w : OWNER) (events : List Event) :
    let wait : PV_STX2_Native.Waiting Data := ⟨req,.child child (.local dest),[]⟩
    let c : Config := ⟨{activation := a,remaining := body,waiting := some wait},parents,s⟩
    PV_THR2_ChildBoundary.delivered base c wait ⟨.returned (.ok value),w,events⟩ =
      ⟨.running ⟨{activation := a,remaining := body},parents,
        write (write s ⟨child,0,[]⟩ (some value)) ⟨a,dest,[]⟩ (some value)⟩,w,events⟩ := rfl

/-- Disjoint source TLS is preserved by native return administration; no
counter equality between caller and child is introduced. -/
theorem frame (s : Store Data) (a child dest : Nat) (value : Data) (q : Address)
    (child_ne : q ≠ (⟨child,0,[]⟩ : Address)) (dest_ne : q ≠ (⟨a,dest,[]⟩ : Address)) :
    (write (write s ⟨child,0,[]⟩ (some value)) ⟨a,dest,[]⟩ (some value)).cells q = s.cells q := by
  rw [write_other _ _ _ _ dest_ne,write_other _ _ _ _ child_ne]

#print axioms delivered
#print axioms frame
end PV_LIB_SPEC_LocalReturn20
