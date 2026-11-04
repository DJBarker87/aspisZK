import NFD_RequestOracle
set_option autoImplicit false
noncomputable section
namespace NFD_RequestDomains
open Aeneas Aeneas.Std Result
abbrev Request := AspisR20Request.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1

theorem payment_length (bytes : Array U8 320#usize) :
    (bytes.val.drop 104).length = 216 := by
  rw [List.length_drop,bytes.property]
  rfl

theorem binding_fields (p : Request) :
    (AspisR1.JHd_RequestCarrier.request p).verifier_profile = p.verifier_profile ∧
    (AspisR1.JHd_RequestCarrier.request p).verifier_release = p.verifier_release ∧
    (AspisR1.JHd_RequestCarrier.request p).pool_program = p.pool_program ∧
    (AspisR1.JHd_RequestCarrier.request p).«public» =
      AspisR1.JHd_RequestCarrier.payment p.«public» := ⟨rfl,rfl,rfl,rfl⟩

/-- No canonical restriction is added at the parser boundary: a payment decoder
receives exactly the216-byte suffix and establishes its own validation. -/
theorem payment_window (bytes : Array U8 320#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=104#usize,«end»:=320#usize}
        core.array.TryFromArrayCopySlice.try_from 216#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=216#usize) bytes 104 (by decide))) :=
  NED_RequestReadWindows.payment bytes

theorem wrong_length (bytes : Slice U8) (bad : bytes.val.length ≠ 320) :
    NFD_RequestOracle.runSlice bytes = ok (.Err AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength) := by
  simp [NFD_RequestOracle.runSlice,core.array.TryFromSharedArraySlice.try_from,Slice.len,Slice.length,bad]

#print axioms wrong_length
#print axioms payment_length
#print axioms binding_fields
#print axioms payment_window
end NFD_RequestDomains
