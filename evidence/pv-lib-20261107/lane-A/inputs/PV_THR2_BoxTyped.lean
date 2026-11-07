import PV_THR2_BoxSelection
import PV_OWN2_Exports
set_option autoImplicit false
noncomputable section
namespace PV_THR2_BoxTyped
open Aeneas Aeneas.Std PV_STX_Machine
open PV_EVHB_OwnerMachine PV_EVHB_RawVecOwner PV_EVHB_OwnerHeap
open PV_OWN2_Codec PV_OWN2_FreshAllocation PV_OWN2_FreshAllocationRefinement
open PV_THR2_BoxRegister

/-- Conditional on owner acceptance of amended translator. Hypotheses:
FreshAllocationValidity' on the registered pre-state, the actual successful
malloc24 reply, and nonnull. No place/header/shape equation is supplied: each
comes from the generated local45 binding and its descriptor registration.
This is a focused allocation cut, not original-entry OwnInit closure. -/
theorem init_memory {W Attr Data Native IoError OsString Scope : Type}
    (carrier : PV_STX2_Store.Carrier W PV_STX2_Syntax.Data)
    (c : PV_STX2_SliceMachine.Config) (w : W) (s : OWNER)
    (resources : Resources) (encode : Encode) (granted : GrantedRegions)
    (pointer : Nat) (handle callback vtable : Pointer)
    (valid : FreshAllocationValidity' resources granted (register carrier c w s))
    (reply : (resources (.malloc 24) (world (register carrier c w s))).answer =
      .returned (.ok pointer)) (nonnull : pointer ≠ 0) :
    let pre := register carrier c w s
    let post := PV_STX_Machine.run (PV_EVHB_SourcePush.handler resources encode) 15
      (PV_OWN2_ConstructorCode.initCode s.next
        (PV_EVHB_SourceLifetimes.emptyHeader shape 8) handle callback vtable) pre
    post.status = .returned (.ok ()) ∧
      PV_OWN2_ThreadInitLayout.InitMemory post.world ⟨⟨c.frame.activation,[45]⟩,[⟨handle,callback,vtable⟩]⟩ := by
  have law := PV_OWN2_Exports.box_init_owned
    (Attr := Attr) (Data := Data) (Native := Native) (IoError := IoError)
    (OsString := OsString) (Scope := Scope) resources encode granted
    (register carrier c w s) ⟨c.frame.activation,[45]⟩ s.next
    (PV_EVHB_SourceLifetimes.emptyHeader shape 8)
  have result := law.BoxTyped pointer handle callback vtable
    (PV_THR2_BoxSelection.place_selected carrier c w s)
    (PV_THR2_BoxSelection.header_selected carrier c w s) rfl valid reply nonnull
  exact ⟨result.1,result.2.1⟩

#print axioms init_memory
end PV_THR2_BoxTyped
