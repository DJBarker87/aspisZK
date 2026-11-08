import PV_LIB_SPEC_Success13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsRecheck13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_TlsBindings13
local instance : DecidableEq Data := Classical.decEq _

/-- Exact source8024 None initializer, not a fabricated native token. -/
def init : Data := match PV_THR2_F170.node12 with
  | .leaf (.aggregateMove _ _ kind []) => PV_THR2_KeyValues.pack kind []
  | _ => .null

def getter : PV_STX2_Native.Request Data :=
  .child (PV_THR2_KeyValues.castToken false).2 8 [init]
def config : Config := ⟨{activation := 1,remaining := []},[],PV_LIB_SPEC_Entry13.store⟩

theorem getter_selected : selected getter = true := by
  change decide ((PV_THR2_KeyValues.castToken false).2 = (PV_THR2_KeyValues.castToken false).2 ∨
    (PV_THR2_KeyValues.castToken false).2 = PV_THR2_F2Call.descriptors.2) = true
  simp only [true_or,eq_self,decide_true]

theorem initializer : (runtime PV_LIB_SPEC_Success13.parameters).control.variant init = some 0 := rfl

/-- The issued source token and source None argument yield an initialized
source reference computed from the SAME concrete entry world/store. This is a
local request application; config is not claimed to be a reached f170 frame. -/
theorem getter_value : value PV_LIB_SPEC_Entry13.slot PV_LIB_SPEC_Success13.parameters
    config PV_LIB_SPEC_Entry13.state getter =
      some (PV_STX2_TypedReferences.reference PV_LIB_SPEC_Entry13.slot.source .null) := by
  unfold value
  simp only [getter,PV_THR2_FnOnceDispatch.request,ite_true]
  rw [initializer]
  change (do
    let _ ← read PV_LIB_SPEC_Entry13.slot PV_LIB_SPEC_Success13.parameters config PV_LIB_SPEC_Entry13.state
    pure (PV_STX2_TypedReferences.reference PV_LIB_SPEC_Entry13.slot.source .null)) = _
  rw [show read PV_LIB_SPEC_Entry13.slot PV_LIB_SPEC_Success13.parameters config
      PV_LIB_SPEC_Entry13.state = some false from PV_LIB_SPEC_Entry13.active]
  rfl

theorem getter_reply :
    reply PV_LIB_SPEC_Entry13.slot PV_LIB_SPEC_Success13.parameters config
      PV_LIB_SPEC_Entry13.state getter
      ⟨.returned (.ok .null),PV_LIB_SPEC_Entry13.state,[]⟩ =
      some ⟨.returned (.ok (PV_STX2_TypedReferences.reference PV_LIB_SPEC_Entry13.slot.source .null)),
        PV_LIB_SPEC_Entry13.state,[]⟩ := by
  unfold reply
  rw [getter_value]
  rfl

#print axioms init
#print axioms getter
#print axioms config
#print axioms getter_selected
#print axioms initializer
#print axioms getter_value
#print axioms getter_reply
end PV_LIB_SPEC_TlsRecheck13
