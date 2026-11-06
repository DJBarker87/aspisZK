import NJT_ClaimsRoot
import NJG_NativeCuts
set_option autoImplicit false
namespace AspisR1.NJT_ClaimsWindows
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open NIX_CertificateFrames
abbrev Row := Array aspis_core.field.QM31 29#usize
abbrev Claims := Array Row 3#usize

theorem row_ext (a b : Row)
 (windows : ∀ (k : Fin 29) (limb : Fin 4),
  NJG_NativeCuts.word (cell a k) limb = NJG_NativeCuts.word (cell b k) limb) : a=b := by
 apply Subtype.ext
 apply List.ext_getElem
 · exact a.property.trans b.property.symm
 · intro i ha hb
   have bound : i<29 := by have h:=a.property;change a.val.length=29 at h;omega
   exact NJG_NativeCuts.word_ext (cell a ⟨i,bound⟩) (cell b ⟨i,bound⟩) (windows ⟨i,bound⟩)

/-- All348 selected words identify the entire returned Claims value. The
windows are precisely those of the native row-write and ownership cuts;
there is no inferred pointee identity from a numeric pointer. -/
theorem claims_ext (a b : Claims)
 (windows : ∀ (p : Fin 3) (k : Fin 29) (limb : Fin 4),
  NJG_NativeCuts.word (cell (cell a p) k) limb = NJG_NativeCuts.word (cell (cell b p) k) limb) : a=b := by
 apply Subtype.ext
 apply List.ext_getElem
 · exact a.property.trans b.property.symm
 · intro i ha hb
   have bound : i<3 := by have h:=a.property;change a.val.length=3 at h;omega
   exact row_ext (cell a ⟨i,bound⟩) (cell b ⟨i,bound⟩) (windows ⟨i,bound⟩)

/-- Reuse the previously proved KMX disjoint-frame induction, including each
aborted prefix; this wrapper supplies the full initialized3-row endpoint. -/
theorem initialized (rows : Fin 3 → Nat → U32) (before : Nat → U32)
 (p : Fin 3) (i : Fin 116) :
 NJG_RowWindows.prefixState rows before 3 (116*p.val+i.val)=rows p i.val :=
 NJG_RowPrefixes.complete_rows rows before p i

#print axioms row_ext
#print axioms claims_ext
#print axioms initialized
end AspisR1.NJT_ClaimsWindows
