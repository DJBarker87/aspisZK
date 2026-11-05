import NHB_Domains
set_option autoImplicit false
namespace AspisR1.NHB_FullFrame
open Aeneas Aeneas.Std

theorem array_ext (left right : Array U32 22#usize)
    (windows : ∀ (j : Nat) (hl : j<left.val.length) (hr : j<right.val.length),
      left.val[j]'hl=right.val[j]'hr) : left=right := by
  apply Subtype.ext
  apply List.ext_getElem
  · exact left.property.trans right.property.symm
  · exact windows

/-- The native arbitrary observation window supplies EVERY cell, including
inactive survivors. This recovers the exact full mutable array frame. -/
theorem survivor_frame (s next : NGQ_SamplerTrace.State) (x : U32) (member : Bool)
    (draws : next.draws.val=s.draws.val+1)
    (length : next.accepted_len.val=s.accepted_len.val+(if member then 0 else 1))
    (windows : ∀ (j : Nat) (hl : j<next.accepted.val.length)
      (hr : j<(if member then s.accepted else s.accepted.set s.accepted_len x).val.length),
      next.accepted.val[j]'hl=
        (if member then s.accepted else s.accepted.set s.accepted_len x).val[j]'hr) :
    NGQ_SamplerStep.Frame s next x member := by
  have arrays := array_ext next.accepted
    (if member then s.accepted else s.accepted.set s.accepted_len x) windows
  refine ⟨draws,length,?_⟩
  cases member <;> simp only [Bool.false_eq_true,↓reduceIte] at arrays ⊢
  · exact congrArg Subtype.val arrays
  · exact congrArg Subtype.val arrays

#print axioms array_ext
#print axioms survivor_frame
end AspisR1.NHB_FullFrame
