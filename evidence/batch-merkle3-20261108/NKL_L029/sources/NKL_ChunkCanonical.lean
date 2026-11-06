import NKL_CanonicalChildren
import MultiproofConeCanonical
set_option autoImplicit false
noncomputable section
namespace NKL_ChunkCanonical
open Aeneas Aeneas.Std Result AspisR1
open OraclePortCompactDraft MultiproofConeCanonical
open NFU_Retarget
attribute [local instance] Classical.propDecidable

theorem le32 (bs : List U8) :
 LPl_Kit_Bytes.le32 bs=little (bytesOf (bs.take 4)) := by
 unfold LPl_Kit_Bytes.le32 little bytesOf
 rw [List.foldr_map]
 rfl

theorem window (bs : List U8) (at width j : Nat) (inside:j<width) :
 (((bs.drop at).take (4*width)).drop (4*j)).take 4=
 (bs.drop (at+4*j)).take 4 := by
 rw [List.drop_take,List.take_take]
 have enough : min 4 (4*width-4*j)=4 := by omega
 rw [enough,List.drop_drop]

/-- A complete width-word chunk is exactly the corresponding canonical-word
block. This relates existing CLOSED child predicates, including rejection. -/
theorem chunk (bs : List U8) (width i : Nat) :
 LPl_Kit_Bytes.validChunk width false ((bs.drop (4*width*i)).take (4*width))=true ↔
 ∀ j,j<width→little (slice (bytesOf bs) (4*(width*i+j)) 4)<2147483647 := by
 simp only [LPl_Kit_Bytes.validChunk,List.all_eq_true,List.mem_range,
   Bool.not_false,Bool.true_or,Bool.and_true,decide_eq_true_eq]
 apply forall_congr'
 intro j
 apply imp_congr_right
 intro inside
 rw [window bs (4*width*i) width j inside,le32]
 simp only [slice,bytesOf,List.map_drop,List.map_take,List.take_take,Nat.min_self]
 have address : 4*width*i+4*j=4*(width*i+j) := by ring
 rw [address]

/-- Structural block/word reindexing. No concrete field enumeration. -/
theorem blocks (bs : List U8) (width : Nat) (positive:0<width)
 (aligned:bs.length%(4*width)=0) :
 LPl_Kit_Bytes.chunksValid (4*width) width false bs=true ↔ canonical (bytesOf bs) := by
 let count:=bs.length/(4*width)
 have length : bs.length=4*(width*count) := by
  have h:=Nat.mod_add_div bs.length (4*width)
  dsimp only [count]
  rw [aligned,Nat.zero_add] at h
  calc bs.length=(4*width)*(bs.length/(4*width)) := h.symm
       _=4*(width*(bs.length/(4*width))) := by ring
 have words : bs.length/4=width*count := by omega
 have mod4 : bs.length%4=0 := by omega
 simp only [LPl_Kit_Bytes.chunksValid,List.all_eq_true,List.mem_range,chunk]
 simp only [canonical,bytesOf,List.length_map,mod4,words,true_and,List.mem_range]
 constructor
 · intro native k bound
   have outer:k/width<count := (Nat.div_lt_iff_lt_mul positive).2 (by omega)
   have inner:k%width<width := Nat.mod_lt k positive
   have h:=native (k/width) outer (k%width) inner
   have address : width*(k/width)+k%width=k := by omega [Nat.mod_add_div k width]
   simpa only [address] using h
 · intro model i outer j inner
   have step : width*(i+1)≤width*count := Nat.mul_le_mul_left width (by omega)
   have bound : width*i+j<width*count := by
    rw [Nat.mul_add,Nat.mul_one] at step
    omega
   exact model (width*i+j) bound

#print axioms le32
#print axioms window
#print axioms chunk
#print axioms blocks
end NKL_ChunkCanonical
end
