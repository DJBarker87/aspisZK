import R1Z.PV_AL_BlockCodec
import R1Z.PV_AL_BlockPrefix
open Aeneas Aeneas.Std Result
namespace R1Z.PV_AL_SplitCarrier
open PV_CBL_GenericArrayPower PV_CBL_LibraryShapes
set_option autoImplicit false

abbrev Block (N : Type) := GenericArray U8 N (Storage U8 6)
def encodeBlock (N : Type) (xs : List U8) : Block N := ⟨PV_AL_BlockCodec.encode 6 xs⟩
def decodeBlock {N : Type} (b : Block N) : List U8 := flatten 6 b.data

def values (N : Type) (v : Slice U8) : List (Block N) :=
  (List.range (v.val.length/64)).map (fun i =>
    encodeBlock N (PV_CBL_SplitModel.block v.val 64 i))

def blockSlice (N : Type) (v : Slice U8) : Slice (Block N) :=
  ⟨values N v,by
    simp only [values,List.length_map,List.length_range]
    exact le_trans (Nat.div_le_self _ _) v.property⟩

def tailSlice (v : Slice U8) : Slice U8 :=
  ⟨v.val.drop ((v.val.length/64)*64),by
    rw [List.length_drop]
    exact le_trans (Nat.sub_le _ _) v.property⟩

def reference (N : Type) (v : Slice U8) : Result (Slice (Block N) × Slice U8) :=
  ok (blockSlice N v,tailSlice v)

theorem decode_values (N : Type) (v : Slice U8) :
    (values N v).map decodeBlock=
      (List.range (v.val.length/64)).map (PV_CBL_SplitModel.block v.val 64) := by
  simp only [values,List.map_map]
  apply List.map_congr_left
  intro i hi
  apply PV_AL_BlockCodec.flatten_encode
  exact PV_CBL_SplitModel.block_length v.val 64 i (List.mem_range.mp hi)

theorem block_bytes (N : Type) (v : Slice U8) :
    ((blockSlice N v).val.map decodeBlock).flatten=
      v.val.take ((v.val.length/64)*64) := by
  rw [show (blockSlice N v).val=values N v from rfl,decode_values,
    ←PV_AL_BlockPrefix.representation]
  exact PV_AL_BlockPrefix.concatenation _ _ _ (Nat.div_mul_le_self _ _)

theorem tail_bytes (v : Slice U8) :
    (tailSlice v).val=v.val.drop ((v.val.length/64)*64) := rfl

theorem total (N : Type) (v : Slice U8) :
    ∃ blocks tail, reference N v=ok (blocks,tail) := ⟨_,_,rfl⟩

#print axioms encodeBlock
#print axioms decodeBlock
#print axioms values
#print axioms blockSlice
#print axioms tailSlice
#print axioms reference
#print axioms decode_values
#print axioms block_bytes
#print axioms tail_bytes
#print axioms total
end R1Z.PV_AL_SplitCarrier
