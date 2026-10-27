import RPu_FJc_FieldBytes
import RPu_FJc_FieldOffsets
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_FieldValue
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE wide)
/-- Field VALUE on the SAME final-message byte slice and source index. -/
theorem value (bytes : Slice U8) (i : Usize) (out : NE) (hi : i.val<64)
    (run : FIo_Native.weights.field bytes i=ok out) :
    FoldedLeafCodec.decodeWide (OraclePortCompactDraft.slice
      (MultiproofConeCanonical.bytesOf bytes.val) (32*i.val) 32)=
        some (AspisR1CurrentWide.Proof.decodeWide (wide out)) := by
  unfold FIo_Native.weights.field at run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨selected,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨o,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases run
  | some x =>
    cases Result.ok.inj run
    have numeric := FJc_FieldBytes.parsed selected out ho
    have data := PSem_Slices.range_bytes bytes selected _ _ hs
    have offsets := FJc_FieldOffsets.value i hi
    have len : (Usize.wrapping_mul (Usize.wrapping_add i 1#usize) 32#usize).val-
        (Usize.wrapping_mul i 32#usize).val=32 := by rw [offsets.1,offsets.2];omega
    rw [data,len,offsets.1] at numeric
    simpa only [MultiproofConeCanonical.bytesOf,List.map_take,List.map_drop,OraclePortCompactDraft.slice] using numeric
#print axioms value
end AspisR1.FJc_FieldValue
end
