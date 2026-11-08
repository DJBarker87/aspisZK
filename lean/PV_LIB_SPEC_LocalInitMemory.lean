import PV_LIB_SPEC_LocalOwnership
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_LocalInitMemory
open PV_STX_Machine PV_STX2_Syntax
open PV_LIB_SPEC_LocalOwnership
/-- Nonvacuous success consequence of the actual local allBridged application:
the24-byte allocation returns12288 and holds the decoded handle/data/vtable.
This is a local source-cut witness, not the missing original-entry history. -/
theorem successful :
    ∃ pointer : PV_OWN2_Codec.Pointer, pointer.val=12288 ∧
      allocationReply.answer = .returned (.ok (PV_THR2_OwnInitPointerCodec.encode pointer)) ∧
      PV_OWN2_ThreadInitLayout.InitMemory post.current.world ⟨⟨1,[45]⟩,[words]⟩ := by
  have result := applied.1
  simpa only [PV_LIB_SPEC_SuccessResources.local_init,
    PV_THR2_OwnInitAllocationCases.Outcome,if_neg (by decide : ¬ (12288:Nat)=0)] using result

/-- The local export's receiver antecedent must not be mistaken for an
actual callback-destination binding. This concrete local data has no39 alias;
the callback allocation is registered at its actual argument backing10/1. -/
theorem no_callback_destination :
    PV_EVHB_OwnerMachine.receiver pre ⟨1,[39]⟩ = none := by
  simp only [PV_EVHB_OwnerMachine.receiver,pre,registered,PV_THR2_BindingRegister.register,
    PV_THR2_LocalBinding.generated]
  rfl

#print axioms successful
#print axioms no_callback_destination
end PV_LIB_SPEC_LocalInitMemory
