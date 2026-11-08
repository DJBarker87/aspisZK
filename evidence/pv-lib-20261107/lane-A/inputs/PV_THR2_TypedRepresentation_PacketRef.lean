import PV_THR2_Spawn361MetadataChild81Reached
set_option autoImplicit false
namespace PV_THR2_TypedRepresentation_PacketRef
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Thread-7 explicit type shape for the shared &Packet returned by Arc::deref
at source13323 (function126). Its address is arbitrary; this asserts no pointee
contents, alias, receiver equality or successful memory read. ClientLayout
pins offsets only; a typed-reference value clause remains a Recount14 input.
Conditional on acceptance of the amended translator. -/
def ValueShape (value : Data) : Prop :=
  ∃ address : Address, value = PV_STX2_TypedReferences.reference address .null
/-- The exact named child's delivered shared-reference representation.
Every other reply and every address remain arbitrary. -/
def Shape {E : Type} (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data) : Prop :=
  ∀ a w argument value,
    (H (.child PV_THR2_Source361PacketChildren.fn81 a [argument]) w).answer =
      .returned (.ok value) → ValueShape value
/-- Hypothesis: the named value shape only. Reference decoding preserves the
arbitrary emitted address and thin metadata; it supplies no stored value. -/
theorem decoded (value : Data) (shape : ValueShape value) :
    ∃ address, PV_STX2_TypedReferences.decode value = some (address,.null) := by
  obtain ⟨address,rfl⟩ := shape
  exact ⟨address,PV_STX2_TypedReferences.roundtrip address .null⟩
#print axioms decoded
end PV_THR2_TypedRepresentation_PacketRef
