import PV_LIB_SLICE_F32
import PV_STX2_SliceF21
set_option autoImplicit false
noncomputable section
namespace PV_LIB_B_F21_F32
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OWNER
abbrev model := @PV_LIB_SLICE_F32.model
abbrev law := @PV_LIB_SLICE_F32.law
abbrev certified := @PV_LIB_SLICE_F32.certified
/-- Keep the complete emitted call, including its unwind cleanup. -/
def sourceNode := PV_STX2_SliceF21.node45
def operandsOf : PV_STX2_SliceSyntax.Node → List Operand
  | .leaf (.call _ _ args _ _) => args
  | _ => []
theorem source_arguments : operandsOf sourceNode = [.move (.local 12),.move (.local 13),.copy (.global 4),.copy (.global 5),.copy (.local 3)] := rfl
def issued (s : Store Data) (src dst : Data) (n : Nat) : Store Data :=
  PV_STX2_Native.arguments s.nextActivation [src,dst,.number 4,.number 4,.number n] 1
    {s with nextActivation := s.nextActivation+1}
/-- Literal f32 domain at the issued five operands. This UB-check contract
requires scalar widths, not an assumed successful copy or pointer validity.
Pointer provenance belongs to the separately named copy contract. -/
theorem caller_domain (s : Store Data) (w : OWNER) (src dst : Data) (n : Nat)
    (wf : PV_STX2_OwnerActivationWellFormed.OwnerWellFormed w s.nextActivation)
    (word : n < PV_STX2_Source7CapacityScalars.modulus) :
    PV_FN_SLICE_f32.Pre (issued s src dst n) s.nextActivation src dst 4 4 n w := by
  refine ⟨PV_STX2_OwnerActivationWellFormed.mono wf (Nat.le_succ _),
    Nat.lt_succ_self _,by decide,by decide,word,?_,?_,?_,?_,?_⟩ <;>
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
        (PV_LIB_SLICE_F32.selectedFuel D K P H s parent parents a w prior)
        (PV_FN_SLICE_f32.start s parent parents a w prior),stack⟩ :
          PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)) := rfl
#print axioms source_arguments
#print axioms caller_domain
#print axioms model
#print axioms law
#print axioms certified
#print axioms actual_machine
end PV_LIB_B_F21_F32
