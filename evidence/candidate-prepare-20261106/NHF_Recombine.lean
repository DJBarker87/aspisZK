import NHF_Expansions
set_option autoImplicit false
namespace AspisR1.NHF_Recombine
open Aeneas Aeneas.Std Result
/-- The actual emitted deref/split back-functions reconstruct the two SAME
callee-produced byte lists. The split guard and replacement lengths are proved. -/
theorem bytes (logical : alloc.vec.Vec U8)
 (deref : Slice U8 × (Slice U8→alloc.vec.Vec U8))
 (parts : (Slice U8×Slice U8) × ((Slice U8×Slice U8)→Slice U8))
 (cut : Usize) (semantic y1 : Slice U8)
 (hderef : lift (alloc.vec.Vec.deref_mut logical)=ok deref)
 (hsplit : core.slice.Slice.split_at_mut deref.1 cut=ok parts)
 (left : semantic.length=parts.1.1.length) (right : y1.length=parts.1.2.length) :
 (deref.2 (parts.2 (semantic,y1))).val=semantic.val++y1.val := by
 have derefEq : alloc.vec.Vec.deref_mut logical=deref := Result.ok.inj hderef
 have bound : cut≤deref.1.length := by
   unfold core.slice.Slice.split_at_mut at hsplit
   split at hsplit
   · assumption
   · cases hsplit
 obtain ⟨pair,call,facts⟩:=WP.spec_imp_exists (core.slice.Slice.split_at_mut.spec deref.1 cut bound)
 have same : pair=parts := Result.ok.inj (call.symm.trans hsplit)
 subst pair
 have firstLength : semantic.length=cut.val := left.trans facts.1
 have secondLength : y1.length=deref.1.length-cut.val := right.trans facts.2.1
 have replacement:=facts.2.2.2.2 semantic y1 firstLength secondLength
 have backCopy:=congrArg (fun p : Slice U8×(Slice U8→alloc.vec.Vec U8)=>
   (p.2 (parts.2 (semantic,y1))).val) derefEq
 change (parts.2 (semantic,y1)).val=(deref.2 (parts.2 (semantic,y1))).val at backCopy
 exact backCopy.symm.trans replacement.1
/-- Both subsequent source borrows are derived from the actual reconstructed
Vec bytes, not supplied as postcondition premises. -/
theorem windows (logical : alloc.vec.Vec U8)
 (deref : Slice U8 × (Slice U8→alloc.vec.Vec U8))
 (parts : (Slice U8×Slice U8) × ((Slice U8×Slice U8)→Slice U8))
 (semantic y1 : Slice U8)
 (hderef : lift (alloc.vec.Vec.deref_mut logical)=ok deref)
 (hsplit : core.slice.Slice.split_at_mut deref.1 13831#usize=ok parts)
 (left : semantic.length=parts.1.1.length) (right : y1.length=parts.1.2.length)
 (semanticSize : semantic.val.length=13831) (ySize : y1.val.length=928) :
 let vector:=deref.2 (parts.2 (semantic,y1))
 vector.val.take 13831=semantic.val ∧ vector.val.drop 13831=y1.val ∧ vector.val.length=14759 := by
 have same:=bytes logical deref parts 13831#usize semantic y1 hderef hsplit left right
 dsimp only
 rw [same]
 exact ⟨NHF_Frame.semantic_preserved _ _ semanticSize,
   NHF_Frame.y1_preserved _ _ semanticSize,NHF_Frame.logical_size _ _ semanticSize ySize⟩
#print axioms bytes
#print axioms windows
end AspisR1.NHF_Recombine
