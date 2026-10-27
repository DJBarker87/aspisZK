import F3P_RecordPacked
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_RecordParsed
open Aeneas Aeneas.Std Result
open ExtractedRecordStrictCodec

theorem parsed (bytes : Slice U8) (value : AspisR1RecordParser.field.wide_exact.WideExact)
    (success : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes=ok (some value)) :
    FoldedLeafCodec.decodeWide (MultiproofConeCanonical.bytesOf bytes.val)=
      some (AspisR1CurrentPreparedClaim.Concrete.decode
        (AspisR1CurrentPreparedClaim.ClaimParser.fromFinish
          (AspisR1CurrentWide.Proof.recordWideToFinish value))) := by
  obtain ⟨len,arr,same,hc,packed⟩ := ExtractedRecordByteCanonicality.slice_success bytes value success
  rw [packed,F3P_RecordPacked.numeric]
  have physical : MultiproofConeCanonical.bytesOf bytes.val=List.ofFn (arrayBytes arr) := by
    rw [arrayBytes_list]
    have h := congrArg Subtype.val same
    rw [← h]
    rfl
  rw [physical]
  simp only [FoldedLeafCodec.decodeWide,ListFieldCodec.fixedBytes?_ofFn,Option.bind_some,
    strict_decode arr hc,Option.map_some]

#print axioms parsed
end AspisR1.F3P_RecordParsed
end
