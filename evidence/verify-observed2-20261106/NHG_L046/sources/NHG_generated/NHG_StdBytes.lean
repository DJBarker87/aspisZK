import NHG_Lengths
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NHG_StdBytes

/-- A literal/tag push on any prior Vec, with capacity established by the
actual serializer prefix. Std allocation/ownership interpretation is retained. -/
theorem push (before : alloc.vec.Vec U8) (byte : U8)
 (cap : before.val.length+1≤Usize.max) :
 ∃ after,alloc.vec.Vec.push before byte=ok after ∧ after.val=before.val++[byte] := by
 unfold alloc.vec.Vec.push
 dsimp only
 rw [dif_pos (by simp only [cap,decide_true,Bool.or_true])]
 exact ⟨_,rfl,List.concat_eq_append⟩

theorem index (before : alloc.vec.Vec U8) (value : U64)
 (cap : before.val.length+8≤Usize.max) :
 ∃ after,alloc.vec.Vec.extend_from_slice core.clone.CloneU8 before
  (Array.to_slice (core.num.U64.to_le_bytes value))=ok after ∧
 after.val=before.val++(core.num.U64.to_le_bytes value).val := by
 apply AspisR1PublicSerializer.FieldsRefinement431.extend_u8
 change before.val.length+(core.num.U64.to_le_bytes value).val.length≤Usize.max
 rw [NHG_Lengths.index]
 exact cap

#print axioms push
#print axioms index
end AspisR1.NHG_StdBytes
