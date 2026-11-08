import PV_LIB_SPEC_UnitReserve17
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_UnitReserveTransport17
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen

/-- Generic symbolic agreement, preserving the entire state including world,
events and suspended frames, outside the native writer polls. This does NOT
assert that all85 actual prefix states have been proved neutral. -/
theorem neutral (p : Parameters) (H : Handler) (q : State)
    (quiet : PV_LIB_StoreActionTable.Neutral PV_LIB_SPEC_Full.programs q) :
    PV_LIB_StoreActionTable.step (runtime p).carrier (runtime p).control
      PV_LIB_SPEC_Full.programs p.resources p.encode H
      (PV_LIB_SPEC_UnitReserve17.values p) q =
    PV_LIB_StoreActionTable.step (runtime p).carrier (runtime p).control
      PV_LIB_SPEC_Full.programs p.resources p.encode H
      (PV_LIB_SPEC_Values14.values p) q := by
  rw [PV_LIB_StoreActionTable.agreement _ _ _ _ _ _ _ _ quiet,
      PV_LIB_StoreActionTable.agreement _ _ _ _ _ _ _ _ quiet]

/-- Successful Unit append uses the actual source headers and the corrected
usize::MAX capacity. The ONLY source writes remain those in the named f10
semantics: destination buf/length, then source length0. No allocation success,
returned RawVec, decoder success, or supplied source Store is assumed. -/
theorem append_graph (p : Parameters) (fn reference other buf inner value source : Data)
    (dest origin : Address) (s : Store Data) (w : OWNER) (events : List Event)
    (len count cap : Nat)
    (unitAppend : PV_THR2_OffPath.functionId fn = some 10)
    (destination : PV_THR2_SourceStoreLibrary.receiver (runtime p).carrier s w reference = some (dest,value))
    (sourceValue : PV_THR2_SourceStoreLibrary.receiver (runtime p).carrier s w other = some (origin,source))
    (raw : (runtime p).carrier.field value 0 = some buf)
    (length : (runtime p).carrier.field value 1 = some (.number len))
    (sourceLength : (runtime p).carrier.field source 1 = some (.number count))
    (buffer : (runtime p).carrier.field buf 0 = some inner)
    (stored : (runtime p).carrier.field inner 1 = some (.number cap))
    (bound : len+count<2^64) :
    PV_THR2_SourceStoreLibrary.PV_THR2_LibrarySemantics_VecAppend10
      (runtime p).carrier (PV_LIB_SPEC_UnitReserve17.values p) fn [reference,other] s w
      ⟨.returned (.ok .null),w,events⟩ =
      (do
        let changed ← writeAddress (runtime p).carrier s
          (PV_THR2_SourceStoreLibrary.withField dest 0) (some buf)
        let changed ← writeAddress (runtime p).carrier changed
          (PV_THR2_SourceStoreLibrary.withField dest 1) (some (.number (len+count)))
        writeAddress (runtime p).carrier changed
          (PV_THR2_SourceStoreLibrary.withField origin 1) (some (.number 0))) := by
  dsimp only [PV_THR2_SourceStoreLibrary.PV_THR2_LibrarySemantics_VecAppend10]
  rw [destination,sourceValue]
  change (do
    let b ← (runtime p).carrier.field value 0
    let .number l ← (runtime p).carrier.field value 1 | none
    let .number c ← (runtime p).carrier.field source 1 | none
    let b' ← (PV_LIB_SPEC_UnitReserve17.values p).reserve fn b l c w ⟨.returned (.ok .null),w,events⟩
    let t ← writeAddress (runtime p).carrier s (PV_THR2_SourceStoreLibrary.withField dest 0) (some b')
    let t ← writeAddress (runtime p).carrier t (PV_THR2_SourceStoreLibrary.withField dest 1) (some (.number (l+c)))
    writeAddress (runtime p).carrier t (PV_THR2_SourceStoreLibrary.withField origin 1) (some (.number 0))) = _
  rw [raw,length,sourceLength]
  change (do
    let b' ← (PV_LIB_SPEC_UnitReserve17.values p).reserve fn buf len count w ⟨.returned (.ok .null),w,events⟩
    let t ← writeAddress (runtime p).carrier s (PV_THR2_SourceStoreLibrary.withField dest 0) (some b')
    let t ← writeAddress (runtime p).carrier t (PV_THR2_SourceStoreLibrary.withField dest 1) (some (.number (len+count)))
    writeAddress (runtime p).carrier t (PV_THR2_SourceStoreLibrary.withField origin 1) (some (.number 0))) = _
  rw [PV_LIB_SPEC_UnitReserve17.unit_no_growth p fn buf inner len count cap w
    ⟨.returned (.ok .null),w,events⟩ unitAppend buffer stored bound]
  rfl

#print axioms neutral
#print axioms append_graph
end PV_LIB_SPEC_UnitReserveTransport17
