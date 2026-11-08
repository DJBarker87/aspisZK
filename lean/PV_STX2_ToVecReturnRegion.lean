import PV_STX2_ToVecConstructorReturn
set_option autoImplicit false
noncomputable section
namespace PV_STX2_ToVecReturnRegion
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER
/-- Conditional on owner acceptance of the translator patch. Reuse any
already proved finite f31 local run under the existing named compatibility.
The arbitrary activation and caller suffix need no activation15 phase marker. -/
theorem native (base : Carrier PV_STX_World.World Data) (K : Control)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (n : Nat) (p q : Prefix OWNER PV_RJ4IDB.NativeEvent)
    (source : advance (PV_STX2_Source7QUniformReturnCompatibility.localCarrier
      (PV_STX2_Source7QUniformReturnCompatibility.C base K H)) K (fun _ => none) H n p = q)
    (defined : ∀ site store, q.status ≠ .undefined site store) :
    advance (PV_STX2_Source7QUniformReturnCompatibility.C base K H) K (fun _ => none) H n p = q := by
  have lifted := PV_STX2_SliceRunExtension.advance_eq
    (PV_STX2_Source7QUniformReturnCompatibility.localCarrier
      (PV_STX2_Source7QUniformReturnCompatibility.C base K H))
    (PV_STX2_Source7QUniformReturnCompatibility.C base K H).aggregate
    (PV_STX2_Source7QUniformReturnCompatibility.preserves base K H)
    K (fun _ => none) H n p (by rw [source]; exact defined)
  rw [PV_STX2_Source7QUniformReturnCompatibility.local_eq] at lifted
  exact lifted.trans source
/-- Conditional on owner acceptance of the translator patch. Replay a
straight generated f31 certificate in the actual installed interpreter, with
its existing finite source result and exact event prefix. -/
theorem straight (resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (nodes rest : List PV_STX2_SliceSyntax.Node) (a : Nat) (parents : List Frame)
    (s : Store Data) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (final : Config)
    (shape : ∀ node ∈ nodes, PV_STX2_Source7QUniformStraightCertificate.Straight node)
    (sites : ∀ node ∈ nodes, match node with
      | .leaf i => PV_STX2_Source7QUniformBindings2.newInstruction i = false
      | _ => True)
    (source : advance (PV_STX2_Source7QUniformReturnCompatibility.localCarrier
      (PV_STX2_Source7QUniformReturnCompatibility.C base K H)) K (fun _ => none) H nodes.length
      ⟨.running ⟨{activation := a,remaining := nodes++rest},parents,s⟩,w,[]⟩ = ⟨.running final,w,[]⟩) :
    PV_STX2_Source7IterationBindings.advance resources encode
      (PV_STX2_Source7QUniformReturnCompatibility.C base K H) K P H nodes.length
      ⟨.running ⟨{activation := a,remaining := nodes++rest},parents,s⟩,w,prior⟩ = ⟨.running final,w,prior⟩ := by
  let C := PV_STX2_Source7QUniformReturnCompatibility.C base K H
  have old := native base K H nodes.length _ _ source (by intro site store bad; cases bad)
  have framed := congrArg (PV_STX2_SlicePrefixEvents.prepend prior) old
  rw [← PV_STX2_SlicePrefixEvents.advance_prepend] at framed
  simp only [PV_STX2_SlicePrefixEvents.prepend,List.append_nil] at framed
  exact (PV_STX2_CallSummaryStraight.run resources encode C K P H nodes rest a parents [] s w prior shape sites).trans
    ((PV_STX2_CallSummaryDispatch.run C K P (fun _ => none) H nodes rest a parents [] s w prior shape).trans framed)
/-- Conditional on owner acceptance of the translator patch. A generated
straight region followed by one neutral control instruction, with no assumed
native answer or source-read premise beyond its already proved local law. -/
theorem last (resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (nodes rest : List PV_STX2_SliceSyntax.Node) (a : Nat) (parents : List Frame)
    (s : Store Data) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (final : Config)
    (shape : ∀ node ∈ nodes, PV_STX2_Source7QUniformStraightCertificate.Straight node)
    (sites : ∀ node ∈ nodes, match node with
      | .leaf i => PV_STX2_Source7QUniformBindings2.newInstruction i = false
      | _ => True)
    (lastShape : ∀ stored, PV_STX2_Source7QUniformAgreement2.configuration
      ⟨{activation := a,remaining := rest},parents,stored⟩)
    (source : advance (PV_STX2_Source7QUniformReturnCompatibility.localCarrier
      (PV_STX2_Source7QUniformReturnCompatibility.C base K H)) K (fun _ => none) H (nodes.length+1)
      ⟨.running ⟨{activation := a,remaining := nodes++rest},parents,s⟩,w,[]⟩ = ⟨.running final,w,[]⟩) :
    PV_STX2_Source7IterationBindings.advance resources encode
      (PV_STX2_Source7QUniformReturnCompatibility.C base K H) K P H (nodes.length+1)
      ⟨.running ⟨{activation := a,remaining := nodes++rest},parents,s⟩,w,prior⟩ = ⟨.running final,w,prior⟩ := by
  let C := PV_STX2_Source7QUniformReturnCompatibility.C base K H
  have old := native base K H (nodes.length+1) _ _ source (by intro site store bad; cases bad)
  have framed := congrArg (PV_STX2_SlicePrefixEvents.prepend prior) old
  rw [← PV_STX2_SlicePrefixEvents.advance_prepend] at framed
  simp only [PV_STX2_SlicePrefixEvents.prepend,List.append_nil] at framed
  exact (PV_STX2_CallSummaryLast.run resources encode C K P (fun _ => none) H
    nodes rest a parents s w prior shape sites lastShape).trans framed
#print axioms native
#print axioms straight
#print axioms last
end PV_STX2_ToVecReturnRegion
