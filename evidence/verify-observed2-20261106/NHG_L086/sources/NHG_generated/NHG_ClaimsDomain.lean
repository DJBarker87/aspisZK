import NHG_ExtraLeaves
import NHG_AppendFrame
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NHG_ClaimsDomain

/-- Each of the three source decode29 requests fits the SAME row25 payload.
This arithmetic does not assert the missing private payload/native bridge. -/
theorem requests (p : Nat) (bound : p<3) :
 p*29+29≤87 ∧ (p*29)*32+29*32≤3712 ∧ 29*(p+1)≤87 := by omega

theorem row_copy {A : Type} (decoded before : Nat→A) (p cell : Nat) :
 KMX_CopyMeaning.loop (fun i=>decoded (i-29*p)) before (29*p) 29 cell=
 if cell/29=p then decoded (cell%29) else before cell := by
 rw [KMX_CopyMeaning.loop_spec]
 by_cases selected : cell/29=p
 · rw [if_pos selected,if_pos (by omega)]
   congr 1
   omega
 · rw [if_neg selected,if_neg (by omega)]

theorem payload_length (framed : Slice U8) (size : framed.val.length=3717) :
 (framed.val.drop 5).length=3712 := by
 rw [List.length_drop,size]
 rfl

theorem round_width (r : Nat) (bound : r<10) :
 15+r≤24 ∧ AspisR1.NGX_PrefixGeometry.width (15+r)=901 := by
 constructor
 · omega
 · unfold AspisR1.NGX_PrefixGeometry.width AspisR1.NFU_PacketDomains.payloadSize
   repeat' first | (solve | omega) | split

theorem fixed_widths : AspisR1.NGX_PrefixGeometry.width 14=37 ∧
 AspisR1.NGX_PrefixGeometry.width 25=3717 := by
 constructor <;> rfl

#print axioms requests
#print axioms row_copy
#print axioms payload_length
#print axioms round_width
#print axioms fixed_widths
end AspisR1.NHG_ClaimsDomain
