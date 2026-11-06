import NIW_AlignFrames
set_option autoImplicit false
namespace AspisR1.NIW_AlignScratch
open Aeneas Aeneas.Std Result NIT_Cuts NIT_PairControl NIW_AlignBoundary

/-- The adopted Vec model is determined by its decoded slice, including its
length. This uses value representation, not physical data-pointer equality. -/
theorem deref_injective (before after : Scratch)
 (same : alloc.vec.Vec.deref before=alloc.vec.Vec.deref after) : before=after := by
 apply Subtype.ext
 exact congrArg Subtype.val same

/-- The observed post-vector is the SAME complete Vec model value used by the
next constructor, not merely a coincident allocation address or a chosen Vec. -/
theorem post (shared : Bool) (address : Nat) (l : NIW_AlignFrames.Stream)
 (afterScratch : Scratch) (afterParts : Parts) (out : Reply Unit)
 (native : NIW_AlignFrames.cutStream shared address l afterScratch afterParts out) :
 afterScratch=l.base.scratchReply := by
 rcases native 0 (by decide) 0 (by decide) 0 (by decide) with ⟨_,_,_,_,_,_,_,_,_,_,_,slice,_⟩
 exact deref_injective afterScratch l.base.scratchReply slice

#print axioms deref_injective
#print axioms post
end AspisR1.NIW_AlignScratch
