import NIL_WindowLayout
set_option autoImplicit false
namespace NIL_HistoryWindows
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- Transport of the producer's per-word predicate, not a producer certificate. -/
theorem round0 (P : List U8 → Prop) (proof : Slice U8)
 (inactive : aspis_core.field.wide_exact.WideExact)
 (history : ∀ i<7,P ((proof.val.drop (7527+32*i)).take 32)) :
 ∀ i<7,P ((((NID_TailView.exactView proof inactive).round0.val).drop (32*i)).take 32) := by
 intro i hi;rw [NIL_WindowLayout.round0 proof inactive i hi];exact history i hi

theorem round1_final (P : List U8 → Prop) (proof : Slice U8)
 (inactive : aspis_core.field.wide_exact.WideExact)
 (history : ∀ i<71,P ((((proof.val.drop 7783).take 2272).drop (32*i)).take 32)) :
 (∀ i<7,P ((((NID_TailView.exactView proof inactive).round1.val).drop (32*i)).take 32)) ∧
 (∀ i<64,P ((((NID_TailView.exactView proof inactive).final_message.val).drop (32*i)).take 32)) := by
 constructor
 · intro i hi
   rw [NIL_WindowLayout.round1 proof inactive i hi]
   have h:=history i (by omega)
   rw [NIL_WindowLayout.block proof.val 7783 2272 i (by omega)] at h
   exact h
 · intro i hi
   rw [NIL_WindowLayout.final proof inactive i hi]
   have h:=history (7+i) (by omega)
   rw [NIL_WindowLayout.scan_final proof.val i hi] at h
   exact h
#print axioms round0
#print axioms round1_final
end NIL_HistoryWindows
