import R1Z.PV_RDCD4_BlockLayout194
import R1Z.PV_RDCD4_Memory194
import R1Z.PV_AL_SplitSelected
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD4_V233
open Aeneas Aeneas.Std Result PV_RDCD4_Memory194

structure BlockSpan where
  pointer : Pointer U8
  count : Nat
structure Views where
  blocks : BlockSpan
  tail : Span U8

/-- Exact source constructors: the block cast preserves the base pointer;
the tail pointer advances by nb*64 bytes. No data is copied or allocated. -/
def source (input : Slice U8) (origin : Nat) : Views :=
  let p : Pointer U8 := ⟨origin,input.val,0⟩
  let n := input.val.length
  let nb := n/64
  let used := nb*64
  ⟨⟨p,nb⟩,sliceRawFromRawParts (advance p used) (n-used)⟩

def blockValues (N : Type) (v : BlockSpan) : List (PV_AL_SplitCarrier.Block N) :=
  (List.range v.count).map (fun i => PV_AL_SplitCarrier.encodeBlock N
    ((v.pointer.data.drop (v.pointer.offset+i*64)).take 64))

def interpreted (N : Type) (input : Slice U8) (origin : Nat) :
    Result (Slice (PV_AL_SplitCarrier.Block N) × Slice U8) :=
  let views := source input origin
  let blocks : Slice (PV_AL_SplitCarrier.Block N) := ⟨blockValues N views.blocks,by
    simp only [blockValues,source,List.length_map,List.length_range]
    exact le_trans (Nat.div_le_self _ _) input.property⟩
  let tail : Slice U8 := ⟨values views.tail,by
    simp only [values,source,sliceRawFromRawParts,ptrSliceFromRawParts,
      metadataFromRawParts,aggregate,advance,List.length_take,List.length_drop]
    have h := input.property
    omega⟩
  ok (blocks,tail)

theorem source_reference (N : Type) (input : Slice U8) (origin : Nat) :
    interpreted N input origin=PV_AL_SplitCarrier.reference N input := by
  apply congrArg Result.ok
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · apply Subtype.ext
    change (input.val.drop ((input.val.length/64)*64)).take
      (input.val.length-(input.val.length/64)*64)=input.val.drop ((input.val.length/64)*64)
    rw [←List.length_drop]
    exact List.take_length _

theorem aliases (input : Slice U8) (origin : Nat) :
    (source input origin).blocks.pointer.origin=origin ∧
    (source input origin).blocks.pointer.offset=0 ∧
    (source input origin).tail.pointer.origin=origin ∧
    (source input origin).tail.pointer.data=input.val ∧
    (source input origin).tail.pointer.offset=(input.val.length/64)*64 :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem valid_tail (input : Slice U8) (origin : Nat) :
    valid (source input origin).tail.pointer (source input origin).tail.len := by
  have hb := PV_RDCD4_BlockLayout194.bounded input.val.length
  simp only [source,sliceRawFromRawParts,ptrSliceFromRawParts,
    metadataFromRawParts,aggregate,advance,valid]
  unfold PV_RDCD4_BlockLayout194.consumed at hb
  omega

#check @PV_AL_SplitSelected.consumed
#print axioms PV_AL_SplitSelected.consumed
#print axioms source_reference
#print axioms aliases
#print axioms valid_tail
end R1Z.PV_RDCD4_V233
