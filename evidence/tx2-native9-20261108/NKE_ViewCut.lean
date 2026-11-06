import NKE_ViewWindows
set_option autoImplicit false
noncomputable section
namespace NKE_ViewCut
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
abbrev E := aspis_core.field.wide_exact.WideExact
/-- Payload transcription of the six current-View windows. Input bytes and
all other caller fields are immutable; the full finish Result is passed on.
Native pointer/length observations remain in the certificate packet. -/
structure Cut (proof : Slice U8) (inactive : E) (out : verifier.View) : Prop where
 variant : out.variant=.S2
 semantic : out.semantic.val=[]
 y1 : out.y1.val=[]
 inactive : out.inactive=inactive
 folded : out.folded_root=none
 query : out.query_bytes.val=[]
 round0Size : out.round0.val.length=224
 round0Cells : ∀ i,i<224 → out.round0.val[i]?=proof.val[7527+i]?
 round1Size : out.round1.val.length=224
 round1Cells : ∀ i,i<224 → out.round1.val[i]?=proof.val[7783+i]?
 finalSize : out.final_message.val.length=2048
 finalWindows : ∀ group,NKE_ViewWindows.Window proof out.final_message group

theorem ext (before after : verifier.View)
 (variant : after.variant=before.variant) (semantic : after.semantic=before.semantic)
 (y1 : after.y1=before.y1) (inactive : after.inactive=before.inactive)
 (round0 : after.round0=before.round0) (folded : after.folded_root=before.folded_root)
 (round1 : after.round1=before.round1) (final : after.final_message=before.final_message)
 (query : after.query_bytes=before.query_bytes) : after=before := by
 cases before
 cases after
 simp_all only []

/-- Six disjoint/native byte windows compose to the SAME current source View;
no canonical-word, history, NoBad or current-proof persistence assumption. -/
theorem same (proof : Slice U8) (inactive : E) (out : verifier.View)
 (length : proof.val.length=57607) (cut : Cut proof inactive out) :
 out=NJR_ViewFinish.view proof inactive := by
 have round0 : out.round0=(NJR_ViewFinish.view proof inactive).round0 := by
  apply Subtype.ext
  exact NKE_ViewWindows.slice_cells proof out.round0 7527 224 (by omega)
   cut.round0Size cut.round0Cells
 have round1 : out.round1=(NJR_ViewFinish.view proof inactive).round1 := by
  apply Subtype.ext
  exact NKE_ViewWindows.slice_cells proof out.round1 7783 224 (by omega)
   cut.round1Size cut.round1Cells
 have final : out.final_message=(NJR_ViewFinish.view proof inactive).final_message := by
  apply Subtype.ext
  exact NKE_ViewWindows.slice_cells proof out.final_message 8007 2048 (by omega)
   cut.finalSize (NKE_ViewWindows.final_cells proof out.final_message cut.finalWindows)
 exact ext _ _ cut.variant (Subtype.ext cut.semantic) (Subtype.ext cut.y1)
  cut.inactive round0 cut.folded round1 final (Subtype.ext cut.query)
#print axioms ext
#print axioms same
end NKE_ViewCut
