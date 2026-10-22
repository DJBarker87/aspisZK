import MultiproofConeParserControl
import MultiproofConePush
import MultiproofConeExpandModel

set_option autoImplicit false
namespace AspisR1.MultiproofConeFrameBuild
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical MultiproofConeSlices MultiproofConeVecLaws
open MultiproofConeParserControl MultiproofConeExpandModel

def frameAndPush (bytes : Slice U8) (logical : alloc.vec.Vec U8)
    (rows : alloc.vec.Vec (alloc.vec.Vec U8)) : Result (alloc.vec.Vec (alloc.vec.Vec U8)) := do
  let prefixBytes ← core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeToUsizeSlice U8) bytes {«end»:=5#usize}
  let framed ← alloc.slice.Slice.to_vec core.clone.CloneU8 prefixBytes
  let framed1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 framed (alloc.vec.Vec.deref logical)
  alloc.vec.Vec.push rows framed1

theorem framing_total (bytes : Slice U8) (logical : alloc.vec.Vec U8)
    (rows : alloc.vec.Vec (alloc.vec.Vec U8)) (bytesBound : 5≤bytes.val.length)
    (logicalBound : logical.val.length≤3712) (rowsBound : rows.val.length≤27) :
    ∃ result, frameAndPush bytes logical rows=ok result ∧
      decodedRows result=decodedRows rows++[(bytesOf bytes.val).take 5++bytesOf logical.val] ∧
      result.val.length=rows.val.length+1 := by
  let prefixBytes := sub bytes 0#usize 5#usize
  have plen : prefixBytes.val.length=5 := by
    simpa only [prefixBytes,show (0#usize).val=0 from rfl,show (5#usize).val=5 from rfl]
      using sub_length bytes 0#usize 5#usize (by scalar_tac) bytesBound
  obtain ⟨frame,hframe,hframeValue⟩ := extend_total prefixBytes (alloc.vec.Vec.deref logical)
    (by change prefixBytes.val.length+logical.val.length≤Usize.max;rw [plen];scalar_tac)
  obtain ⟨result,hresult,hresultValue⟩ := MultiproofConePush.push_total rows frame (by scalar_tac)
  refine ⟨result,?_,?_,?_⟩
  · simp only [frameAndPush,prefix_total bytes 5#usize bytesBound,to_vec_bytes,bind_tc_ok]
    change (do let framed1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 prefixBytes
                  (alloc.vec.Vec.deref logical)
               alloc.vec.Vec.push rows framed1)=ok result
    rw [hframe]
    exact hresult
  · have prefixMeaning : bytesOf prefixBytes.val=(bytesOf bytes.val).take 5 := by
      simp only [prefixBytes,bytes_sub,show (0#usize).val=0 from rfl,show (5#usize).val=5 from rfl,
        OraclePortCompactDraft.slice,Nat.sub_zero,List.drop_zero]
    have frameMeaning : bytesOf frame.val=(bytesOf bytes.val).take 5++bytesOf logical.val := by
      rw [hframeValue,bytes_append,prefixMeaning]
      rfl
    simp only [decodedRows,hresultValue,List.map_append,List.map_cons,List.map_nil,frameMeaning]
  · simp only [hresultValue,List.length_append,List.length_cons,List.length_nil]

#print axioms framing_total
end AspisR1.MultiproofConeFrameBuild
