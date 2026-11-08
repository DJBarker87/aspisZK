import PV_LIB_SLICE_F33
import PV_STX2_SliceF21
set_option autoImplicit false
noncomputable section
namespace PV_LIB_B_F21_F33
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OWNER
abbrev model := @PV_LIB_SLICE_F33.model
abbrev law := @PV_LIB_SLICE_F33.law
abbrev certified := @PV_LIB_SLICE_F33.certified
/-- Keep the complete emitted call, including its unwind cleanup. -/
def sourceNode := PV_STX2_SliceF21.node65
def operandsOf : PV_STX2_SliceSyntax.Node → List Operand
  | .leaf (.call _ _ args _ _) => args
  | _ => []
theorem source_arguments : operandsOf sourceNode = [.copy (.local 3),.move (.local 15)] := rfl
def issued (s : Store Data) (n cap : Nat) : Store Data :=
  PV_STX2_Native.arguments s.nextActivation [.number n,.number cap] 1
    {s with nextActivation := s.nextActivation+1}
/-- Both usize operands are retained; no length<=capacity premise is added.
The failure/panic comparison is part of the provider's own graph. -/
theorem caller_domain (s : Store Data) (w : OWNER) (n cap : Nat)
    (wf : PV_STX2_OwnerActivationWellFormed.OwnerWellFormed w s.nextActivation)
    (nw : n < PV_STX2_Source7CapacityScalars.modulus)
    (cw : cap < PV_STX2_Source7CapacityScalars.modulus) :
    PV_FN_SLICE_f33.Pre (issued s n cap) s.nextActivation n cap w := by
  refine ⟨PV_STX2_OwnerActivationWellFormed.mono wf (Nat.le_succ _),
    Nat.lt_succ_self _,nw,cw,?_,?_⟩ <;>
    simp [issued,PV_STX2_Native.arguments,write]

/-- The graph is the actual supplied-machine run at the selected certified
prefix, not an independently chosen reply. `certified` supplies eligibility
and the bound on this exact fuel. No first-boundary strengthening is claimed. -/
theorem actual_machine (D : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_W5_UbCheckPrimitives.Handler)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    law D K P H s parent parents a w prior stack
      (PV_LIB.observe (⟨PV_STX2_SliceMachine.advance D K P H
        (PV_LIB_SLICE_F33.selectedFuel D K P H s parent parents a w prior)
        (PV_FN_SLICE_f33.start s parent parents a w prior),stack⟩ :
          PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)) := rfl
#print axioms source_arguments
#print axioms caller_domain
#print axioms model
#print axioms law
#print axioms certified
#print axioms actual_machine
end PV_LIB_B_F21_F33
