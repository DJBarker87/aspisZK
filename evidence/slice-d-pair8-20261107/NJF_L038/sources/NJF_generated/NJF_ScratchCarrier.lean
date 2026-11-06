import NIW_AlignScratch
set_option autoImplicit false
namespace AspisR1.NJF_ScratchCarrier
open Aeneas Aeneas.Std Result NIT_Cuts NIT_PairControl

/-- The array-backed oracle in K006/K007 covers EVERY decoded borrowed-slice
post of length64, including posts of an actual heap-backed Vec. These are
payload values; no physical allocation or equal-address implication is used. -/
def array64 (v : Scratch) (length : (alloc.vec.Vec.deref v).val.length=64) : Array K 64#usize :=
 ⟨(alloc.vec.Vec.deref v).val,length⟩

theorem covers (v : Scratch) (length : (alloc.vec.Vec.deref v).val.length=64) :
 ∃ a : Array K 64#usize,a.val=(alloc.vec.Vec.deref v).val := ⟨array64 v length,rfl⟩

/-- The complete source Vec value is determined by the full observed array.
Representation changes to oracle setup do not introduce a new caller domain. -/
theorem injective (v w : Scratch)
 (lv : (alloc.vec.Vec.deref v).val.length=64) (lw : (alloc.vec.Vec.deref w).val.length=64)
 (same : array64 v lv=array64 w lw) : v=w := by
 apply NIW_AlignScratch.deref_injective
 apply Subtype.ext
 exact congrArg Subtype.val same

#print axioms covers
#print axioms injective
end AspisR1.NJF_ScratchCarrier
