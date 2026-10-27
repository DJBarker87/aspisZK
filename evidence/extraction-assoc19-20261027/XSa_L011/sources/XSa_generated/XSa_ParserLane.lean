import XSa_ParserRange
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XSa_ParserLane
open AspisR1ClaimPreparedBridge

def field (s : Slice U8) (lane : Nat) : Result C.E := do
 let bytes ← XRn_Join_sliceRange s (32*lane) (32*lane+32)
 let opt ← _root_.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes
 match opt with
 | none => fail .panic
 | some e => ok e

theorem lane (s : Slice U8) (n : Nat) (hn : n<29) :
 mapR toClaimE (field s n) =
 AspisR1CurrentPreparedClaim.ClaimParser.field s (XRn_Join_usize n) := by
 let i := XRn_Join_usize n
 have hi : i.val=n := XRy_ClaimSelect.usize_value n (by omega)
 obtain ⟨start,hs,hsv⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=i) (y:=32#usize) (by scalar_tac))
 obtain ⟨next,hnx,hnv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
 obtain ⟨finish,hf,hfv⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=next) (y:=32#usize) (by scalar_tac))
 have hstart : start.val=32*n := by scalar_tac
 have hfinish : finish.val=32*n+32 := by scalar_tac
 unfold AspisR1CurrentPreparedClaim.ClaimParser.field AspisR1CurrentWide.Proof.finishField
   AspisR1WeightsFieldCurrent.weights.field
 change mapR toClaimE (field s n) = (do
   let a ← i*32#usize
   let b ← i+1#usize
   let c ← b*32#usize
   let selected ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) s ⟨a,c⟩
   let opt ← AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes selected
   let value ← core.option.Option.unwrap opt
   ok (AspisR1CurrentPreparedClaim.ClaimParser.fromFinish (AspisR1CurrentWide.Proof.recordWideToFinish value)))
 rw [hs,bind_tc_ok,hnx,bind_tc_ok,hf,bind_tc_ok,XSa_ParserRange.range,hstart,hfinish]
 unfold field
 simp only [mapR_bind,bind_map]
 apply congrArg (fun k => XRn_Join_sliceRange s (32*n) (32*n+32) >>= k)
 funext selected
 rw [XSa_ParserTotal.bytes]
 simp only [mapR_bind,bind_map]
 apply congrArg (fun k => AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes selected >>= k)
 funext opt
 cases opt <;> rfl

#print axioms lane
end XSa_ParserLane
