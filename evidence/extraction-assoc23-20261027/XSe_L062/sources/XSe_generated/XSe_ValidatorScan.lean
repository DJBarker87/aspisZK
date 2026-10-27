import XSe_ChunkList
import XSe_BooleanScan
import XSe_FoldCongruence
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_ValidatorScan
open XSe_ValidatorStage

def good (s : Slice U8) : Bool := XRn_Join_Bytes.validChunk 8 true s.val
/-- All actual chunk stages, with the exact first failing enumeration index. -/
theorem chunks (row : U8) (items : List (Slice U8)) (i : Usize)
 (sizes : ∀ c∈items,c.val.length=32)
 (bound : i.val+items.length≤UScalar.cMax .Usize) :
 XRo_Join_Carriers.mapR XSe_EnumeratedDriver.finish
  (XSe_ListDriver.fold (XSe_EnumeratedDriver.step XSe_ValidatorIter.next (kit row)) items (.Ok i))=
 XSe_BooleanScan.result (fun i => OldError.NonCanonical row i)
  (XSe_BooleanScan.first good items i.val) := by
 rw [XSe_FoldCongruence.source
  (XSe_EnumeratedDriver.step XSe_ValidatorIter.next (kit row))
  (XSe_EnumeratedDriver.step XSe_ValidatorIter.next
   (XSe_BooleanScan.stage good (fun i => OldError.NonCanonical row i))) items ?_ (.Ok i)]
 · exact XSe_BooleanScan.source good _ items i bound
 · intro c hc count
   unfold XSe_EnumeratedDriver.step
   rw [XSe_ChunkStage.source row count c (sizes c hc)]
   rfl
/-- Complete emitted validator at the source-selected standard chunk list.
Tails are retained as an ignored remainder, with no payload bound assumption. -/
theorem source (row : U8) (payload : Slice U8) :
 AspisR1PrefixAggregateParser.r1_wire.validate_record_fields row payload=
 XSe_BooleanScan.result (fun i => OldError.NonCanonical row i)
  (XSe_BooleanScan.first good (XSe_ChunkList.slices payload) 0) := by
 rw [XSe_ValidatorFold.source]
 unfold XSe_ValidatorFold.run core.slice.Slice.chunks_exact
 rw [dif_pos (by decide)]
 simp only [bind_tc_ok,core.iter.traits.iterator.Iterator.enumerate.trait_default,
  core.iter.traits.iterator.Iterator.enumerate.default]
 apply chunks row (XSe_ChunkList.slices payload) 0#usize (XSe_ChunkList.size payload)
 rw [XSe_ChunkList.count]
 have h := payload.property
 change 0+payload.val.length/32≤_
 exact Nat.le_trans (Nat.div_le_self _ _) h
#print axioms chunks
#print axioms source
end XSe_ValidatorScan
