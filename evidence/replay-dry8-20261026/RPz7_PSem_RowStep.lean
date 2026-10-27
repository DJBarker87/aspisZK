import RPz7_PSem_Control
import PSem_Shapes
import PSem_Values
import RecordPayloadPartition
set_option autoImplicit false
noncomputable section
namespace AspisR1.PSem_RowStep
open Aeneas Aeneas.Std Result PSem_Control
open AspisS1NativeCompact AspisS1NativeCompactBodyFrame
open AspisS1ValuesOwnedInstallation MultiproofConeCanonical OraclePortCompactDraft

private theorem copied (dst src out : Slice U8)
    (h : core.slice.Slice.copy_from_slice core.marker.CopyU8 dst src=ok out) : out=src := by
  unfold core.slice.Slice.copy_from_slice at h
  split at h
  · exact (Result.ok.inj h).symm
  · cases h

private theorem window_length (input window : Slice U8) (back : Slice U8 → Slice U8)
    (start stop : Usize)
    (h : core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice U8)
      input {start:=start,«end»:=stop}=ok (window,back)) :
    window.val.length=stop.val-start.val := by
  simp only [Slice.index_mut_SliceIndexRangeUsizeSliceInst] at h
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index_mut at h
  split at h
  · have same := congrArg (fun p : Slice U8 × (Slice U8 → Slice U8) => p.1.val.length)
      (Result.ok.inj h)
    simp only [List.slice_length] at same
    scalar_tac
  · cases h

/-- Exact bytes appended by one successful source semantic-expansion row.
The header and payload reads, copy lenses and value-expansion result all come
from this step. This theorem assumes no child output or byte agreement. -/
theorem row_bytes (input out updated : Slice U8)
    (iter nextIter actualIter : core.ops.range.Range U8) (row tag : U8) (size src dst nextSrc nextDst : Usize)
    (advance : core.iter.range.IteratorRange.next core.iter.range.StepU8 iter=ok (some row,nextIter))
    (shape : r1_wire.row_shape row=ok (some (tag,size)))
    (call : compact.expand_semantic_loop.body nativeValues input iter out src dst=
      ok (.cont (actualIter,updated,nextSrc,nextDst))) :
    actualIter=nextIter ∧
    nextSrc.val=src.val+5+(if 14 ≤ row.val then size.val/2 else size.val) ∧
    nextDst.val=dst.val+5+size.val ∧
    nextSrc.val ≤ input.val.length ∧
    bytesOf (updated.val.take nextDst.val)=bytesOf (out.val.take dst.val) ++
      (bytesOf (input.val.drop src.val)).take 5 ++
      (if 14 ≤ row.val then
        expand (size.val/32) (bytesOf ((input.val.drop (src.val+5)).take (size.val/2)))
       else bytesOf ((input.val.drop (src.val+5)).take size.val)) := by
  unfold compact.expand_semantic_loop.body at call
  obtain ⟨next,it,hit,call⟩ := pair_success _ _ _ call
  have nextEq := Result.ok.inj (hit.symm.trans advance)
  have oEq : next=some row := congrArg Prod.fst nextEq
  have itEq : it=nextIter := congrArg Prod.snd nextEq
  subst next
  subst it
  obtain ⟨actualShape,hshape,call⟩ := bind_success _ _ _ call
  have shapeEq : actualShape=some (tag,size) := Result.ok.inj (hshape.symm.trans shape)
  subst actualShape
  simp (config := {zeta := true}) only [core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at call
  obtain ⟨headerEnd,hheaderEnd,call⟩ := bind_success _ _ _ call
  obtain ⟨header,back,hheader,call⟩ := pair_success _ _ _ call
  obtain ⟨sourceHeaderEnd,hsourceHeaderEnd,call⟩ := bind_success _ _ _ call
  obtain ⟨sourceHeader,hsourceHeader,call⟩ := bind_success _ _ _ call
  obtain ⟨newHeader,hnewHeader,call⟩ := bind_success _ _ _ call
  have hdest := add_value dst 5#usize headerEnd hheaderEnd
  have hsource := add_value src 5#usize sourceHeaderEnd hsourceHeaderEnd
  change headerEnd.val=dst.val+5 at hdest
  change sourceHeaderEnd.val=src.val+5 at hsource
  have copyHeader := copied header sourceHeader newHeader hnewHeader
  have headerRead := PSem_Slices.range_bytes input sourceHeader src sourceHeaderEnd hsourceHeader
  have headerLength := PSem_Slices.range_length input sourceHeader src sourceHeaderEnd hsourceHeader
  have headerSize : newHeader.val.length=headerEnd.val-dst.val := by
    rw [copyHeader,headerLength]
    change sourceHeaderEnd.val-src.val=headerEnd.val-dst.val
    change headerEnd.val=dst.val+5 at hdest
    change sourceHeaderEnd.val=src.val+5 at hsource
    omega
  have headerPrefix := PSem_Lenses.range_prefix out header back dst headerEnd hheader newHeader headerSize
  have compactCall := PSem_Shapes.compact_flag row
  rw [compactCall] at call
  simp only [bind_tc_ok,decide_eq_true_eq] at call
  by_cases compactRow : 14 ≤ row.val
  · simp only [compactRow,if_true] at call
    obtain ⟨half,hhalf,call⟩ := bind_success _ _ _ call
    obtain ⟨sourceEnd,hsourceEnd,call⟩ := bind_success _ _ _ call
    obtain ⟨sourcePayload,hsourcePayload,call⟩ := bind_success _ _ _ call
    obtain ⟨payloadEnd,hpayloadEnd,call⟩ := bind_success _ _ _ call
    obtain ⟨payload,backPayload,hpayload,call⟩ := pair_success _ _ _ call
    obtain ⟨status,replacement,hexpand,call⟩ := pair_success _ _ _ call
    cases status with
    | Err error =>
      change ok (ControlFlow.done (.Err error,backPayload replacement) : ControlFlow State Exit)=
        ok (ControlFlow.cont (actualIter,updated,nextSrc,nextDst) : ControlFlow State Exit) at call
      cases call
    | Ok unit =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at call
      obtain ⟨sourceNext,hsourceNext,call⟩ := bind_success _ _ _ call
      have same := ControlFlow.cont.inj (Result.ok.inj call)
      simp only [Prod.mk.injEq] at same
      rcases same with ⟨sameIter,sameBuf,sameSrc,sameDst⟩
      subst actualIter
      subst updated
      subst nextSrc
      subst nextDst
      have hv := div_two size half hhalf
      have hs := add_value sourceHeaderEnd half sourceEnd hsourceEnd
      have hn := add_value sourceHeaderEnd half sourceNext hsourceNext
      have hd := add_value headerEnd size payloadEnd hpayloadEnd
      have bytes := PSem_Values.source_expansion sourcePayload payload replacement hexpand
      have sourceRead := PSem_Slices.range_bytes input sourcePayload sourceHeaderEnd sourceEnd hsourcePayload
      have sourceLength := PSem_Slices.range_length input sourcePayload sourceHeaderEnd sourceEnd hsourcePayload
      have values := AspisS1ValuesOwnedInstallation.accepted_bytes sourcePayload payload replacement hexpand
      have payloadLength := window_length (back newHeader) payload backPayload headerEnd payloadEnd hpayload
      have replacementSize : replacement.val.length=payloadEnd.val-headerEnd.val :=
        values.1.trans payloadLength
      have payloadPrefix := PSem_Lenses.range_prefix (back newHeader) payload backPayload
        headerEnd payloadEnd hpayload replacement replacementSize
      refine ⟨rfl,by simp only [if_pos compactRow];omega,by omega,?_,?_⟩
      · have bound := PSem_Slices.range_bounds input sourcePayload sourceHeaderEnd sourceEnd hsourcePayload
        omega
      · rw [payloadPrefix,headerPrefix]
        rw [MultiproofConeExpandModel.bytes_append,MultiproofConeExpandModel.bytes_append]
        rw [show bytesOf replacement.val=expand (size.val/32)
          (bytesOf ((input.val.drop (src.val+5)).take (size.val/2))) from ?_]
        · rw [copyHeader,headerRead]
          have offset : sourceHeaderEnd.val=src.val+5 := by exact hsource
          have width : sourceHeaderEnd.val-src.val=5 := by omega
          simp only [width,bytesOf,List.map_take,List.map_append,if_pos compactRow]
        · rw [bytes,sourceRead]
          have width : sourceEnd.val-sourceHeaderEnd.val=size.val/2 := by omega
          have length : sourcePayload.length=size.val/2 := by change sourcePayload.val.length=_;omega
          have quotient : sourcePayload.length/16=size.val/32 := by omega
          rw [quotient,width,show sourceHeaderEnd.val=src.val+5 from hsource]
  · simp only [compactRow,if_false] at call
    obtain ⟨payloadEnd,hpayloadEnd,call⟩ := bind_success _ _ _ call
    obtain ⟨payload,backPayload,hpayload,call⟩ := pair_success _ _ _ call
    obtain ⟨sourceEnd,hsourceEnd,call⟩ := bind_success _ _ _ call
    obtain ⟨sourcePayload,hsourcePayload,call⟩ := bind_success _ _ _ call
    obtain ⟨replacement,hcopy,call⟩ := bind_success _ _ _ call
    have same := ControlFlow.cont.inj (Result.ok.inj call)
    simp only [Prod.mk.injEq] at same
    rcases same with ⟨sameIter,sameBuf,sameSrc,sameDst⟩
    subst actualIter
    subst updated
    subst nextSrc
    subst nextDst
    have hd := add_value headerEnd size payloadEnd hpayloadEnd
    have hs := add_value sourceHeaderEnd size sourceEnd hsourceEnd
    have copyPayload := copied payload sourcePayload replacement hcopy
    have sourceRead := PSem_Slices.range_bytes input sourcePayload sourceHeaderEnd sourceEnd hsourcePayload
    have sourceLength := PSem_Slices.range_length input sourcePayload sourceHeaderEnd sourceEnd hsourcePayload
    have replacementSize : replacement.val.length=payloadEnd.val-headerEnd.val := by
      rw [copyPayload,sourceLength]
      omega
    have payloadPrefix := PSem_Lenses.range_prefix (back newHeader) payload backPayload
      headerEnd payloadEnd hpayload replacement replacementSize
    refine ⟨rfl,by simp only [if_neg compactRow];omega,by omega,?_,?_⟩
    · exact (PSem_Slices.range_bounds input sourcePayload sourceHeaderEnd sourceEnd hsourcePayload).2
    · rw [payloadPrefix,headerPrefix,copyPayload,copyHeader,headerRead,sourceRead]
      have headerWidth : sourceHeaderEnd.val-src.val=5 := by omega
      have payloadWidth : sourceEnd.val-sourceHeaderEnd.val=size.val := by omega
      rw [headerWidth,payloadWidth,show sourceHeaderEnd.val=src.val+5 from hsource]
      simp only [bytesOf,List.map_append,List.map_take,if_neg compactRow]
#print axioms window_length
#print axioms copied
#print axioms row_bytes
end AspisR1.PSem_RowStep
end
