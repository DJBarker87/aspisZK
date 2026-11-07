import PV_STX2_ToVecF31Regions
import PV_STX2_ToVecF31Return
set_option autoImplicit false
noncomputable section
namespace PV_STX2_ToVecF31Suffix
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER
/-- Conditional on owner acceptance of the translator patch. Compose the
existing generated f31 regions on the installed interpreter. The actual
computed store and arbitrary caller suffix survive the whole return. -/
theorem source33 (resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a cap : Nat)
    (ptr alloc : Data) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent)
    (bounded : cap < PV_STX2_Source7CapacityScalars.modulus)
    (input : s.cells ⟨a,0,[]⟩ = some (PV_STX2_Aggregates.pack
      PV_STX2_Source7QHeaderStep.kind [ptr,.number cap,alloc]))
    (requested : s.cells ⟨a,1,[]⟩ = some (.number cap))
    (layout : s.cells ⟨a,3,[]⟩ = some PV_STX2_Source7LayoutConstructor.value) :
    let K := PV_STX2_Source7QF31Assert.control ctrl
    PV_STX2_Source7IterationBindings.advance resources encode
      (PV_STX2_Source7QUniformReturnCompatibility.C base K H) K P H 33
      ⟨.running ⟨{activation := a,remaining := PV_STX2_Source7CtorF31.program.body.drop 9},parent::parents,s⟩,w,prior⟩ =
      ⟨.running ⟨{activation := a,remaining := [PV_STX2_Source7CtorF31.node63],completed := some (.ok
        (PV_STX2_Aggregates.pack PV_STX2_Source7QHeaderStep.kind [ptr,.number cap,alloc]))},
        parent::parents,PV_STX2_Source7QF31Suffix.stored s a cap⟩,w,prior⟩ := by
  dsimp only
  let K := PV_STX2_Source7QF31Assert.control ctrl
  rw [show 33=7+26 by omega,PV_STX2_Source7IterationBindings.advance_add,
    PV_STX2_ToVecF31Regions.source7 resources encode base K P H s (parent::parents) a w prior layout,
    show 26=4+22 by omega,PV_STX2_Source7IterationBindings.advance_add,
    PV_STX2_ToVecF31Regions.source4 resources encode base K P H _ (parent::parents)
      (PV_STX2_Source7CtorF31.program.body.drop 16) a cap ptr alloc w prior
      (by simp [PV_STX2_Source7QF31Layout.stored,write,input]),
    show 22=9+13 by omega,PV_STX2_Source7IterationBindings.advance_add,
    PV_STX2_ToVecF31Regions.source9 resources encode base ctrl P H _ (parent::parents) a cap w prior bounded
      (by simp [PV_STX2_Source7QF31Capacity.stored,write])
      (by simp [PV_STX2_Source7QF31Capacity.stored,PV_STX2_Source7QF31Layout.stored,write,requested])]
  exact PV_STX2_ToVecF31Return.source13 resources encode base K P H _ parent parents a _ w prior
    (by simp [PV_STX2_Source7QF31Assert.stored,PV_STX2_Source7QF31Capacity.stored,
      PV_STX2_Source7QF31Layout.stored,write,input])
    (by simp [PV_STX2_Source7QF31Assert.stored,write])
    (by simp [PV_STX2_Source7QF31Assert.stored,write])
/-- Conditional on owner acceptance of the translator patch. Completed f31
binds its actual result into the original saved f21 LOCAL8 and retains all
callee-written cells; no native successful f31 reply is assumed. -/
theorem binding1 (resources : Resources) (encode : Encode)
    (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (s post : Store Data) (parents : List Frame) (a : Nat)
    (length alloc layout inner : Data) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) :
    PV_STX2_Source7IterationBindings.advance resources encode C K P H 1
      ⟨.running ⟨{activation := s.nextActivation,remaining := [PV_STX2_Source7CtorF31.node63],completed := some (.ok inner)},
        (PV_STX2_SliceToVecEntry.called s parents a length alloc layout).frame::parents,post⟩,w,prior⟩ =
      ⟨.running {(PV_STX2_SliceToVecEntry.called s parents a length alloc layout) with
        store := write (write post ⟨s.nextActivation,0,[]⟩ (some inner)) ⟨a,8,[]⟩ (some inner),
        frame := {(PV_STX2_SliceToVecEntry.called s parents a length alloc layout).frame with waiting := none}},w,prior⟩ := by
  have old := PV_STX2_Source7QF31Return.binding1 C K P H s post parents a length alloc layout inner w
  have same := PV_STX2_ToVecAllocateReturn.completed resources encode C K P P H
    ⟨{activation := s.nextActivation,remaining := [PV_STX2_Source7CtorF31.node63],completed := some (.ok inner)},
      (PV_STX2_SliceToVecEntry.called s parents a length alloc layout).frame::parents,post⟩ w (.ok inner) rfl
  simpa only [PV_STX2_Source7IterationBindings.advance,PV_STX2_SliceMachine.advance,
    same,PV_STX2_SlicePrefixEvents.prepend,List.nil_append,List.append_nil] using
    congrArg (PV_STX2_SlicePrefixEvents.prepend prior) old
#print axioms source33
#print axioms binding1
end PV_STX2_ToVecF31Suffix
