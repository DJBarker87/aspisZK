import NKI_ValuePrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_ValueTotal
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_ValuePrefix (Openings Selectors Tail)
def Canonical (t : Tail) : Prop := Canon t.selector ∧ canonical t.range
/-- Full SAME original opening carrier is returned by all3source loops. -/
theorem source (o : Openings) (s : Selectors)
 (hz : canonical o.z) (hs : canonical o.succ_z) (hx : canonical o.xor12_z)
 (hh : canonical s.high) (hl : canonical s.low) :
 NKI_ValuePrefix.run o s ⦃ t=>t.openings=o ∧ Canonical t ⦄ := by
 have zero:=FIv_NativeValue.zero.1
 have zeros:=JFy_ZeroArrays.source 33#usize
 unfold NKI_ValuePrefix.run
 step*
 all_goals first | assumption | scalar_tac | (subst_vars;unfold Canonical;exact ⟨rfl,by assumption,by assumption⟩)
#print axioms source
end AspisR1.NKI_ValueTotal
end
