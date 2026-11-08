import PV_LIB_SPEC_TlsAt85
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveReplacement16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_TlsNative15 (reference)

/-- Local documented Cell::replace binding, retaining the old scalar and the
one physical byte write. The original8248 call is NOT reached by this lemma. -/
theorem physical (p : Parameters) (c : Config) (w : OWNER)
    (active : PV_LIB_SPEC_TlsBindings13.read PV_LIB_SPEC_Entry13.slot p c w = some false) :
    PV_LIB_SPEC_CellPhysical13.reply PV_LIB_SPEC_Entry13.slot p c w
      [reference,.boolean true] ⟨.returned (.ok .null),w,[]⟩ =
      some ⟨.returned (.ok (.boolean false)),
        PV_LIB_SPEC_CellPhysical13.setByte PV_LIB_SPEC_Entry13.slot w true,[]⟩ := by
  have address : (runtime p).carrier.dereference w reference = some PV_LIB_SPEC_Entry13.slot.source := by
    simp only [reference,runtime,PV_THR2_OwnInitExactReturnedCases.carrier,
      PV_THR2_EntryDynamic.carrier,PV_THR2_Scalars.carrier,
      PV_STX2_TypedReferences.carrier,PV_STX2_TypedReferences.roundtrip]
  unfold PV_LIB_SPEC_CellPhysical13.reply
  dsimp only
  rw [address]
  simp only [ite_true,Option.bind_some,active]
  rfl

/-- Source write graph of the existing named289 semantics. Native physical
memory and source store are separate channels, never a supplied Store delta. -/
theorem source_write (p : Parameters) (s : Store Data) (w : OWNER) :
    PV_THR2_SourceStoreLibrary.PV_THR2_LibrarySemantics_CellReplace289
      (runtime p).carrier [reference,.boolean true] s w =
      some (write s PV_LIB_SPEC_Entry13.slot.source (some (.boolean true))) := by
  have address : (runtime p).carrier.dereference w reference = some PV_LIB_SPEC_Entry13.slot.source := by
    simp only [reference,runtime,PV_THR2_OwnInitExactReturnedCases.carrier,
      PV_THR2_EntryDynamic.carrier,PV_THR2_Scalars.carrier,
      PV_STX2_TypedReferences.carrier,PV_STX2_TypedReferences.roundtrip]
  unfold PV_THR2_SourceStoreLibrary.PV_THR2_LibrarySemantics_CellReplace289
  dsimp only
  rw [address]
  simp [writeAddress,PV_LIB_SPEC_Entry13.slot]

#print axioms physical
#print axioms source_write
end PV_LIB_SPEC_ActiveReplacement16
