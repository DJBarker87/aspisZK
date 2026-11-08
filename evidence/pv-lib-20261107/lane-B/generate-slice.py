from pathlib import Path
for num in [32,33]:
 m=f'PV_LIB_B_F21_F{num}'
 s=f'''import PV_LIB_SLICE_F{num}
import PV_STX2_SliceF21
set_option autoImplicit false
noncomputable section
namespace {m}
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OWNER
abbrev model := @PV_LIB_SLICE_F{num}.model
abbrev law := @PV_LIB_SLICE_F{num}.law
abbrev certified := @PV_LIB_SLICE_F{num}.certified
/-- Keep the complete emitted call, including its unwind cleanup. -/
def sourceNode := PV_STX2_SliceF21.node{45 if num==32 else 65}
def operandsOf : PV_STX2_SliceSyntax.Node → List Operand
  | .leaf (.call _ _ args _ _) => args
  | _ => []
'''
 args='[.move (.local 12),.move (.local 13),.copy (.global 4),.copy (.global 5),.copy (.local 3)]' if num==32 else '[.copy (.local 3),.move (.local 15)]'
 s+=f'theorem source_arguments : operandsOf sourceNode = {args} := rfl\n'
 if num==32:
  s+='''def issued (s : Store Data) (src dst : Data) (n : Nat) : Store Data :=
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
'''
 else:
  s+='''def issued (s : Store Data) (n cap : Nat) : Store Data :=
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
'''
 s+=f'''
/-- The graph is the actual supplied-machine run at the selected certified
prefix, not an independently chosen reply. `certified` supplies eligibility
and the bound on this exact fuel. No first-boundary strengthening is claimed. -/
theorem actual_machine (D : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_W5_UbCheckPrimitives.Handler)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    law D K P H s parent parents a w prior stack
      (PV_LIB.observe (⟨PV_STX2_SliceMachine.advance D K P H
        (PV_LIB_SLICE_F{num}.selectedFuel D K P H s parent parents a w prior)
        (PV_FN_SLICE_f{num}.start s parent parents a w prior),stack⟩ :
          PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)) := rfl
#print axioms source_arguments
#print axioms caller_domain
#print axioms model
#print axioms law
#print axioms certified
#print axioms actual_machine
end {m}
'''
 Path('lean',m+'.lean').write_text(s)
