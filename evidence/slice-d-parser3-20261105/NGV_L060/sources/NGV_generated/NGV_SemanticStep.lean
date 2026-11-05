import NGV_SemanticHeader
import NGV_SemanticLow
import NGV_SemanticHigh
import NGV_Cursors
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_SemanticStep
open AspisS1NativeCompact NGV_RowPayload
/-- One actual original emitted iteration, with both closed child packets
substituted at their exact original borrowed windows and arbitrary prestate. -/
theorem result (input before : Slice U8) (row : U8) (live : row.val<27)
 (inputSize : input.val.length=7015) (outputSize : before.val.length=13831)
 (packet : Packet input before row.val) :
 ∃ next : U8,next.val=row.val+1 ∧
 compact.expand_semantic_loop.body AspisS1ValuesOwnedInstallation.nativeValues input
   {start:=row,«end»:=27#u8} before (NGV_Cursors.src row.val (by omega)) (NGV_Cursors.dst row.val (by omega))=
 ok (.cont ({start:=next,«end»:=27#u8},after packet,
   NGV_Cursors.src (row.val+1) (by omega),NGV_Cursors.dst (row.val+1) (by omega))) := by
 obtain ⟨next,nextValue,iterator⟩:=NGV_SemanticArithmetic.next row live
 obtain ⟨tag,size,shape⟩:=NGD_RowPayload.present row live
 have sourceShape : r1_wire.row_shape row=ok (some (tag,size)) := by
   rw [←NGD_RowPayload.compact_shape];exact shape
 have sizeValue:=NGD_RowPayload.exact_size row tag size live shape
 have advance:=NGV_Cursors.advance row.val live size sizeValue
 refine ⟨next,nextValue,?_⟩
 rw [NGV_SemanticHeader.result AspisS1ValuesOwnedInstallation.nativeValues input before
   {start:=row,«end»:=27#u8} {start:=next,«end»:=27#u8} row tag
   (NGV_Cursors.src row.val (by omega)) (NGV_Cursors.dst row.val (by omega))
   (NGV_Cursors.srcHead row.val live) (NGV_Cursors.dstHead row.val live) size
   live inputSize outputSize rfl rfl rfl rfl iterator sourceShape]
 by_cases high : 14≤row.val
 · obtain ⟨half,division,halfValue⟩:=NGV_SemanticArithmetic.div size
   have storedValue : half.val=NGD_SemanticSchedule.stored row.val := by
     simp only [NGD_SemanticSchedule.stored,if_pos high]
     rw [halfValue,sizeValue]
   exact NGV_SemanticHigh.result input before row {start:=next,«end»:=27#u8}
     (NGV_Cursors.srcHead row.val live) (NGV_Cursors.dstHead row.val live)
     (NGV_Cursors.src (row.val+1) (by omega)) (NGV_Cursors.dst (row.val+1) (by omega)) size half
     live high inputSize outputSize rfl rfl sizeValue storedValue division
     (by simpa only [halfValue] using advance.2.2 high) advance.1 packet
 · exact NGV_SemanticLow.result input before row {start:=next,«end»:=27#u8}
     (NGV_Cursors.srcHead row.val live) (NGV_Cursors.dstHead row.val live)
     (NGV_Cursors.src (row.val+1) (by omega)) (NGV_Cursors.dst (row.val+1) (by omega)) size
     live (by omega) inputSize outputSize rfl rfl sizeValue (advance.2.1 (by omega)) advance.1 packet
#print axioms result
end NGV_SemanticStep
