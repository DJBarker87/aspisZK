import PV_W5_F31Carrier
import PV_W5_F31SuccessStore
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace PV_W5_F31SuccessJoin
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER
open PV_STX2_SliceMachine

abbrev cut (s : Store Data) (a n pointer : Nat) :=
  PV_W5_F31SuccessStore.returned s a (.number n) PV_STX2_Source7GlobalClone.value
    PV_STX2_Source7LayoutConstructor.value
    (PV_STX2_Source7QConstructorResult.value (PV_W5_F35Success.inner pointer n PV_STX2_Source7GlobalClone.value))
abbrev extracted (s : Store Data) (a n pointer : Nat) :=
  PV_STX2_Source7QResultIntoF31.stored (cut s a n pointer) a
    (PV_W5_F35Success.inner pointer n PV_STX2_Source7GlobalClone.value)

/-- Reuse the named payload extraction and complete return suffix on the
single installed carrier. Inputs are derived from the native call setup. -/
theorem source35 (resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (ctrl : Control) (H : PV_W5_F35Modes.HType)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a n pointer : Nat)
    (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent)
    (live : a<s.nextActivation) (bounded : n<PV_STX2_Source7CapacityScalars.modulus)
    (requested : s.cells ⟨a,1,[]⟩=some (.number n))
    (layout : s.cells ⟨a,3,[]⟩=some PV_STX2_Source7LayoutConstructor.value) :
    PV_STX2_Source7IterationBindings.advance resources encode (PV_FN_SLICE_f31.C base ctrl H)
      (PV_FN_SLICE_f31.L ctrl) (fun _ => none) H 35
      ⟨.running ⟨{activation:=a,remaining:=PV_STX2_Source7CtorF31.program.body.drop 7},parent::parents,
        cut s a n pointer⟩,w,prior⟩ =
      ⟨.running ⟨{activation:=a,remaining:=[PV_STX2_Source7CtorF31.node63],completed:=some (.ok
        (PV_W5_F35Success.inner pointer n PV_STX2_Source7GlobalClone.value))},parent::parents,
        PV_STX2_Source7QF31Suffix.stored (extracted s a n pointer) a n⟩,w,prior⟩ := by
  rw [PV_FN_SLICE_f31.C,PV_W5_F31Carrier.installed]
  have first := PV_STX2_ToVecConstructorExtract.source2 resources encode base
    (PV_STX2_Source7QF31Assert.control ctrl) (fun _ => none) H (cut s a n pointer)
    (parent::parents) [] a (PV_W5_F35Success.inner pointer n PV_STX2_Source7GlobalClone.value) w prior
    (by simp [cut,PV_W5_F31SuccessStore.returned,write])
  simp only [List.append_nil] at first
  have controls : PV_STX2_Source7QAllocationCall.control (PV_STX2_Source7QF31Assert.control ctrl) =
      PV_FN_SLICE_f31.L ctrl := rfl
  rw [controls] at first
  have last := PV_STX2_ToVecF31Suffix.source33 resources encode base
    (PV_STX2_Source7QAllocationCall.control ctrl) (fun _ => none) H (extracted s a n pointer)
    parent parents a n (PV_STX2_Source7QHeaderOperands.pointerValue pointer) PV_STX2_Source7GlobalClone.value
    w prior bounded
    (by simp [extracted,PV_STX2_Source7QResultIntoF31.stored,write,PV_W5_F35Success.inner])
    (by
      simpa [extracted,PV_STX2_Source7QResultIntoF31.stored,write] using
        (PV_W5_F31SuccessStore.argument s a 1 _ _ _ _ live (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)).trans requested)
    (by
      simpa [extracted,PV_STX2_Source7QResultIntoF31.stored,write] using
        (PV_W5_F31SuccessStore.argument s a 3 _ _ _ _ live (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)).trans layout)
  rw [show 35=2+33 by omega,PV_STX2_Source7IterationBindings.advance_add,first]
  exact last

#print axioms source35
end PV_W5_F31SuccessJoin
