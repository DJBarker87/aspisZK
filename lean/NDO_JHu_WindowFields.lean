import NDO_NCV_FieldViews
import JHu_ReferenceBytes
import JHu_ReferenceWords
import JHu_ZeroFields
set_option autoImplicit false
namespace AspisR1.JHu_WindowFields
open Aeneas Aeneas.Std Result

theorem field (b : Slice U8) (a n s w : Nat) (fit : s+w ≤ n) :
    ((JHg_FieldRead.segment b a n).val.drop s).take w=(b.val.drop (a+s)).take w :=
  congrArg Subtype.val (NCV_FieldViews.nested b a n s w fit)
#print axioms field

theorem byte (b : Slice U8) (a n : Nat) (s : Usize) (x : U8)
    (bound : a+n ≤ b.val.length) (fit : s.val<n)
    (value : (b.val.drop (a+s.val)).take 1=[x]) :
    Slice.index_usize (JHg_FieldRead.segment b a n) s=ok x := by
  apply NCV_FieldViews.byte
  · rw [JHg_FieldRead.length b a n bound];exact fit
  · rw [field b a n s.val 1 (by omega)]
    exact value
#print axioms byte

theorem bytes32 (b : Slice U8) (a n : Nat) (s : Usize) (out : Array U8 32#usize)
    (bound : a+n ≤ b.val.length) (cap : n ≤ 768) (fit : s.val+32 ≤ n)
    (value : (b.val.drop (a+s.val)).take 32=out.val) :
    NCV_Reference.bytes32 (JHg_FieldRead.segment b a n) s=ok out := by
  apply JHu_ReferenceBytes.bytes32
  · rw [JHg_FieldRead.length b a n bound];exact cap
  · rw [JHg_FieldRead.length b a n bound];exact fit
  · rw [field b a n s.val 32 fit]
    exact value
#print axioms bytes32
end AspisR1.JHu_WindowFields
