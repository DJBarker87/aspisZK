import NKI_RangeCohort
import NKI_ArrayCanonicalEq
import NDO_JFy_ValueBits
import RPv_JFy_ZeroArrays
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_RangeAssociation
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon decode)
open NJX_RangeInvocation (Openings xs zero)
/-- All native3×10step/frame packets, exact ZERO33initialization, and complete
raw-array equality with the SAME emitted three-loop source invocation. -/
theorem source (o : Openings) (hz : FIw_ArrayValue.canonical o.z)
 (hs : FIw_ArrayValue.canonical o.succ_z) (hx : FIw_ArrayValue.canonical o.xor12_z) :
 ∃ a b c,
 NJX_RangeFold.run 0 (xs o 0) (List.finRange 10) zero=ok a ∧
 NJX_RangeFold.Trace 0 (xs o 0) (List.finRange 10) zero a ∧
 NJX_RangeFold.run 1 (xs o 1) (List.finRange 10) a=ok b ∧
 NJX_RangeFold.Trace 1 (xs o 1) (List.finRange 10) a b ∧
 NJX_RangeFold.run 2 (xs o 2) (List.finRange 10) b=ok c ∧
 NJX_RangeFold.Trace 2 (xs o 2) (List.finRange 10) b c ∧
 (∀ j,Canon (c j)) ∧
 FIx_ValueBitPrefix.calls o (Array.repeat 33#usize field.QM31.ZERO)=ok (o,NJB_ArrayCarrier.array (N:=33#usize) c) := by
 have hc:=NJX_RangeInvocation.canonical o hz hs hx
 obtain ⟨a,ca,ta,ha,va⟩ := NJX_RangeFold.source 0 (xs o 0) (hc 0) (List.finRange 10) zero (fun _=>FIv_NativeValue.zero.1)
 obtain ⟨b,cb,tb,hb,vb⟩ := NJX_RangeFold.source 1 (xs o 1) (hc 1) (List.finRange 10) a ha
 obtain ⟨c,cc,tc,hcc,vc⟩ := NJX_RangeFold.source 2 (xs o 2) (hc 2) (List.finRange 10) b hb
 have values : (fun j=>decode (c j))=FIx_ValueBitPrefix.model o (fun _=>0) := by
  rw [vc,vb,va]
  change (List.finRange 10).foldl _ ((List.finRange 10).foldl _ ((List.finRange 10).foldl _ (fun _=>decode field.QM31.ZERO)))=_
  simp only [FIv_NativeValue.zero.2]
  rw [NKI_RangeModel.source,NKI_RangeModel.source,NKI_RangeModel.source]
  exact NKI_RangeCohort.source o
 obtain ⟨r,cr,hr,vr⟩ := JFy_ValueBits.source o (Array.repeat 33#usize field.QM31.ZERO) hz hs hx (JFy_ZeroArrays.source _)
 have canon:=NJB_ArrayCarrier.canonical_array (N:=33#usize) c hcc
 have arrValues : FIw_ArrayValue.decoded (NJB_ArrayCarrier.array (N:=33#usize) c)=(fun j=>decode (c j)) := by
  funext j
  change decode (NJB_ArrayCarrier.cell (NJB_ArrayCarrier.array (N:=33#usize) c) j)=_
  rw [NJB_ArrayCarrier.cell_array]
 have same : r=NJB_ArrayCarrier.array (N:=33#usize) c := by
  apply NKI_ArrayCanonicalEq.source r _ hr canon
  rw [vr,FIx_ArrayMeaning.decoded_repeat,FIv_NativeValue.zero.2,arrValues,values]
 exact ⟨a,b,c,ca,ta,cb,tb,cc,tc,hcc,by simpa only [same] using cr⟩
#print source
#print axioms source
end AspisR1.NKI_RangeAssociation
end
