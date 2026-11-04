import R1Z.PV_RDCD4_BlockLayout194
import R1Z.PV_RDCD4_Memory194
import R1Z.PV_AL_SplitSelected
import R1Z.PV_RDCD5_BlockCarrier
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD5_V233
open Aeneas Aeneas.Std Result PV_RDCD4_Memory194

structure BlockSpan where
  pointer : Pointer U8
  count : Nat
structure Views where
  blocks : BlockSpan
  tail : Span U8

/-- A native typed block is recovered exactly from its byte view. This
rules out a merely byte-equal replacement of a distinct storage tree. -/
theorem typed_roundtrip (N : Type) (block : PV_AL_SplitCarrier.Block N) :
    PV_AL_SplitCarrier.encodeBlock N (PV_AL_SplitCarrier.decodeBlock block) = block := by
  cases block with
  | mk data =>
    unfold PV_AL_SplitCarrier.encodeBlock PV_AL_SplitCarrier.decodeBlock
    rw [PV_RDCD5_BlockCarrier.encode_flatten]

theorem typed_projection_injective (N : Type) :
    Function.Injective (PV_AL_SplitCarrier.decodeBlock (N := N)) := by
  intro a b h
  have e := congrArg (PV_AL_SplitCarrier.encodeBlock N) h
  rwa [typed_roundtrip,typed_roundtrip] at e

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
    simp only [views,blockValues,source,List.length_map,List.length_range]
    exact le_trans (Nat.div_le_self _ _) input.property⟩
  let tail : Slice U8 := ⟨values views.tail,by
    simp only [views,values,source,sliceRawFromRawParts,ptrSliceFromRawParts,
      metadataFromRawParts,aggregate,advance,List.length_take,List.length_drop]
    have h := input.property
    omega⟩
  ok (blocks,tail)

theorem source_reference (N : Type) (input : Slice U8) (origin : Nat) :
    interpreted N input origin=PV_AL_SplitCarrier.reference N input := by
  apply congrArg Result.ok
  apply Prod.ext
  · apply Subtype.ext
    simp only [interpreted,source,blockValues,PV_AL_SplitCarrier.reference,
      PV_AL_SplitCarrier.blockSlice,PV_AL_SplitCarrier.values,PV_CBL_SplitModel.block,Nat.zero_add]
  · apply Subtype.ext
    simp only [source,values,sliceRawFromRawParts,ptrSliceFromRawParts,
      metadataFromRawParts,aggregate,advance,PV_AL_SplitCarrier.tailSlice,Nat.zero_add]
    change (input.val.drop ((input.val.length/64)*64)).take
      (input.val.length-(input.val.length/64)*64)=input.val.drop ((input.val.length/64)*64)
    rw [←List.length_drop]
    exact List.take_length

theorem aliases (input : Slice U8) (origin : Nat) :
    (source input origin).blocks.pointer.origin=origin ∧
    (source input origin).blocks.pointer.offset=0 ∧
    (source input origin).tail.pointer.origin=origin ∧
    (source input origin).tail.pointer.data=input.val ∧
    (source input origin).tail.pointer.offset=(input.val.length/64)*64 :=
  by simp [source,sliceRawFromRawParts,ptrSliceFromRawParts,metadataFromRawParts,aggregate,advance]

theorem valid_tail (input : Slice U8) (origin : Nat) :
    valid (source input origin).tail.pointer (source input origin).tail.len := by
  have hb := PV_RDCD4_BlockLayout194.bounded input.val.length
  simp only [source,sliceRawFromRawParts,ptrSliceFromRawParts,
    metadataFromRawParts,aggregate,advance,valid]
  unfold PV_RDCD4_BlockLayout194.consumed at hb
  omega

/-- The source's interpreted typed carrier is the precise selected Eager
split consumed by the existing callback, for every valid input slice. -/
theorem consumed_instance (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_AL_SplitNativeShape.Types base))
    (input : Slice U8) (origin : Nat) :
    letI : ProverRwFull.ExternalTypes := PV_AL_SplitNativeShape.Types base
    interpreted (PV_AL_SplitNativeShape.Size base 6) input origin =
      (@ProverRwFull.block_buffer.Eager.Insts.Block_bufferSealedSealed
        (PV_AL_SplitNativeShape.Types base)
        (PV_AL_SplitSelected.selected base ops)).split_blocks
          (PV_AL_SplitNativeShape.nativeTrait base ops 6) input := by
  rw [source_reference,PV_AL_SplitSelected.consumed] <;> rfl

#print axioms typed_roundtrip
#print axioms typed_projection_injective
#print axioms source_reference
#print axioms aliases
#print axioms valid_tail
#print axioms consumed_instance
end R1Z.PV_RDCD5_V233
