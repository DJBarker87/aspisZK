import NID_TailView
set_option autoImplicit false
namespace NIL_WindowLayout
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

theorem block {A : Type} (bytes : List A) (start count i : Nat) (inside : 32*(i+1)≤count) :
 (((bytes.drop start).take count).drop (32*i)).take 32=
 (bytes.drop (start+32*i)).take 32 := by
 rw [List.drop_take,List.take_take,List.drop_drop]
 rw [Nat.min_eq_left (by omega)]

theorem round0 (proof : Slice U8) (inactive : aspis_core.field.wide_exact.WideExact)
 (i : Nat) (inside : i<7) :
 (((NID_TailView.exactView proof inactive).round0.val).drop (32*i)).take 32=
 (proof.val.drop (7527+32*i)).take 32 := block proof.val 7527 224 i (by omega)

theorem round1 (proof : Slice U8) (inactive : aspis_core.field.wide_exact.WideExact)
 (i : Nat) (inside : i<7) :
 (((NID_TailView.exactView proof inactive).round1.val).drop (32*i)).take 32=
 (proof.val.drop (7783+32*i)).take 32 := block proof.val 7783 224 i (by omega)

theorem final (proof : Slice U8) (inactive : aspis_core.field.wide_exact.WideExact)
 (i : Nat) (inside : i<64) :
 (((NID_TailView.exactView proof inactive).final_message.val).drop (32*i)).take 32=
 (proof.val.drop (8007+32*i)).take 32 := block proof.val 8007 2048 i (by omega)

/-- canonical_scan's fourth echeck covers71 consecutive words:7 round1 +64 final. -/
theorem scan_final (proof : List U8) (i : Nat) (inside : i<64) :
 (((proof.drop 7783).take 2272).drop (32*(7+i))).take 32=
 (proof.drop (8007+32*i)).take 32 := by
 rw [block proof 7783 2272 (7+i) (by omega)]
 congr 2
 omega

#print axioms block
#print axioms round0
#print axioms round1
#print axioms final
#print axioms scan_final
end NIL_WindowLayout
