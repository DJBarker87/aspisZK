import NKJ_Arrays
set_option autoImplicit false
namespace NKJ_Small2
open Aeneas Aeneas.Std Result NKJ_Arrays

theorem literal (l0 l1 r0 r1 : Q) :
 NKJ_Extracted.field.NKJ_reference.NKJ_small2 (encode (Array.make 2#usize [l0,l1])) (encode (Array.make 2#usize [r0,r1]))=
 NKJ_Loop.run [(l0,r0),(l1,r1)] := by
 simp [NKJ_Extracted.field.NKJ_reference.NKJ_small2,encode,Array.make,Array.index_usize,
  NKJ_Extracted.field.NKJ_reference.NKJ_words,NKJ_Cache.words,NKJ_Extracted.fromCanonical,
  NKJ_Loop.run,NKJ_Loop.loop,NGA_Small.zero,bind_assoc_eq]

theorem source (left right : Array Q 2#usize)
 (hl : ∀ x∈left.val, NGA_Cache.Canonical x) (hr : ∀ x∈right.val, NGA_Cache.Canonical x) :
 NKJ_Extracted.field.NKJ_reference.NKJ_small2 (encode left) (encode right)=
 (do let q ← NGA_Wrappers.sum2 left right;ok (NKJ_Extracted.fromCanonical q)) := by
 obtain ⟨l0,l1,hlshape⟩ := List.length_eq_two.mp left.property
 obtain ⟨r0,r1,hrshape⟩ := List.length_eq_two.mp right.property
 have heleft : left=Array.make 2#usize [l0,l1] := Subtype.ext hlshape
 have heright : right=Array.make 2#usize [r0,r1] := Subtype.ext hrshape
 obtain ⟨_,domain⟩ := NGA_Wrappers.domain left right hl hr
 rw [heleft,heright] at domain ⊢
 rw [literal]
 exact NKJ_Loop.value [(l0,r0),(l1,r1)] (by simp) domain
#print axioms literal
#print axioms source
end NKJ_Small2
