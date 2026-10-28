import NCX_FieldLaws
import JHu_ZeroFields
import NCV_FieldViews
set_option autoImplicit false
namespace NCX_ZeroLaws
open Aeneas Aeneas.Std Result AspisR1

theorem zero (b : Slice U8) (n : Nat) (h : b.val=List.replicate n 0#u8)
    (cap : n ≤ 768) : NCX_Reference.zero b=ok true := by
  have same : NCX_Reference.zero b=NCV_Reference.zero b := rfl
  rw [same,JHu_ZeroFields.zero b n h cap]
theorem nonzero (b : Slice U8) (cap : b.val.length ≤ 768)
    (first : NCV_ZeroStep.byte b 0 ≠ 0#u8) (len : 0<b.val.length) :
    NCX_Reference.zero b=ok false := by
  have same : NCX_Reference.zero b=NCV_Reference.zero b := rfl
  rw [same,JHu_ZeroFields.nonzero b cap first len]
theorem magic (b : Slice U8) (m : Array U8 4#usize)
    (fit : 4 ≤ b.val.length) (field : b.val.take 4=m.val) :
    NCX_Reference.magic b m=ok true := by
  have read:=NCV_FieldViews.read_prefix b 4#usize fit
  have eq : NCX_Reference.equal (JHg_FieldRead.segment b 0 4) m.to_slice=ok true := by
    rw [NCX_FieldLaws.equal _ _ (by rw [JHg_FieldRead.length _ 0 4 (by omega)];omega)]
    have h : (JHg_FieldRead.segment b 0 4).val=m.to_slice.val := by
      simpa only [JHg_FieldRead.segment,List.drop_zero,Array.to_slice] using field
    simp only [h,decide_true]
  simpa only [NCX_Reference.magic,read,lift,bind_tc_ok] using eq

#print axioms zero
#print axioms nonzero
#print axioms magic
end NCX_ZeroLaws
