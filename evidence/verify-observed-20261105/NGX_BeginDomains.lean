import NGX_PrefixCarrier
import NGX_ValidatedTrace
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NGX_BeginDomains
/-- The source producer's exact widths establish every begin leaf's frame
bound. This is the same framed window, not an unrelated successful token. -/
theorem frame_domain (row : Nat) (begin_row : row≤14) (framed : Slice U8)
 (same_width : framed.val.length=NGX_PrefixGeometry.width row) :
 row≤24 ∧ framed.val.length≤3717 := by
 have width:=NGX_PrefixGeometry.widths row
 omega

theorem cursor_step (row next : U8) (begin_row : row.val≤14)
 (same : next=row) : ∃ after,
 (next+1#u8 : Result U8)=ok after ∧ after.val=row.val+1 ∧ after.val≤15 := by
 have domain:=NGX_SemanticDomain.arithmetic row (by omega)
 obtain ⟨tag,after,htag,hafter,tvalue,avalue⟩:=domain
 subst next
 exact ⟨after,hafter,avalue,by omega⟩

theorem root_domain : NGX_PrefixGeometry.start 0=32 ∧ 32≤57607 := by
 exact ⟨NGX_PrefixGeometry.start_zero,by decide⟩
#print axioms frame_domain
#print axioms cursor_step
#print axioms root_domain
end AspisR1.NGX_BeginDomains
