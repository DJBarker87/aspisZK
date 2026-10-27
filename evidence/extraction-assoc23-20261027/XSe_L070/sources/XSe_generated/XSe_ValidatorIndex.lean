import XSe_ValidatorScan
import XSe_ChunkAt
import XSe_FirstIndex
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_ValidatorIndex

def bad (payload : Slice U8) (i : Nat) : Bool :=
 !XRn_Join_Bytes.validChunk 8 true ((payload.val.drop (32*i)).take 32)
/-- SAME source window and SAME full first-error index, including all tails. -/
theorem source (payload : Slice U8) :
 XSe_BooleanScan.first XSe_ValidatorScan.good (XSe_ChunkList.slices payload) 0=
 (List.range (payload.val.length/32)).find? (bad payload) := by
 let fallback : Slice U8 := ⟨[],by decide⟩
 have scan := XSe_FirstIndex.source XSe_ValidatorScan.good fallback (bad payload)
  (XSe_ChunkList.slices payload) 0 ?_
 · simpa only [XSe_ChunkList.count,←List.range_eq_range'] using scan
 · intro j hj
   unfold bad XSe_ValidatorScan.good
   rw [XSe_ChunkAt.source payload j hj fallback]
   rfl
#print axioms source
end XSe_ValidatorIndex
