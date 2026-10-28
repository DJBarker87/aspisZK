import NDO_JGi_FieldCell
set_option autoImplicit false
namespace AspisR1.JHm_FieldValue
open Aeneas Aeneas.Std Result
open AspisR1CurrentPreparedClaim
open AspisR1.ExtractedRecordByteCanonicality

def value (arr : Array U8 32#usize) : Concrete.E :=
  ClaimParser.fromFinish (AspisR1CurrentWide.Proof.recordWideToFinish
    (AspisR1.ExtractedRecordLimbCanonicality.packed
      (wordLE arr 0) (wordLE arr 1) (wordLE arr 2) (wordLE arr 3)
      (wordLE arr 4) (wordLE arr 5) (wordLE arr 6) (wordLE arr 7)))

/-- Strengthens the inherited totality result with the actual decoded value. -/
theorem source (bytes : Slice U8) (i : Usize) (arr : Array U8 32#usize)
    (fits : 32*(i.val+1)≤bytes.length) (small : bytes.length≤20000)
    (selected : (bytes.val.drop (32*i.val)).take 32=arr.val)
    (bounds : ∀ j : Fin 8,(wordLE arr j).val<2147483647) :
    ClaimParser.field bytes i=ok (value arr) := by
  obtain ⟨start,mul,hs⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=i) (y:=32#usize) (by scalar_tac))
  obtain ⟨next,add,hn⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
  obtain ⟨stop,mulStop,ht⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=next) (y:=32#usize) (by scalar_tac))
  have order : start≤stop := by scalar_tac
  have bound : stop.val≤bytes.length := by scalar_tac
  obtain ⟨slice,range,contents,size⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      (⟨start,stop⟩ : core.ops.range.Range Usize) bytes order bound)
  have range' : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
      {start:=start,«end»:=stop}=ok slice := range
  have same : slice=Array.to_slice arr := by
    apply Subtype.ext
    rw [contents]
    change (bytes.val.drop start.val).take (stop.val-start.val)=arr.val
    have hstart : start.val=32*i.val := by scalar_tac
    have width : stop.val-start.val=32 := by scalar_tac
    rw [width,hstart,selected]
  let w := AspisR1.ExtractedRecordLimbCanonicality.packed
    (wordLE arr 0) (wordLE arr 1) (wordLE arr 2) (wordLE arr 3)
    (wordLE arr 4) (wordLE arr 5) (wordLE arr 6) (wordLE arr 7)
  have parser : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some w) :=
    (fixed_success_iff arr w).mpr ⟨bounds,rfl⟩
  unfold ClaimParser.field AspisR1CurrentWide.Proof.finishField AspisR1WeightsFieldCurrent.weights.field
  rw [mul,bind_tc_ok,add,bind_tc_ok,mulStop,bind_tc_ok,range',bind_tc_ok,same,parser,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JHm_FieldValue
