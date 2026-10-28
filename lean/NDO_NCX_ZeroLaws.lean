import NDO_NCX_FieldLaws
import NDO_NCV_FieldViews
set_option autoImplicit false
namespace NCX_ZeroLaws
open Aeneas Aeneas.Std Result AspisR1

theorem zero (b : Slice U8) (n : Nat) (h : b.val=List.replicate n 0#u8)
    (cap : n ≤ 768) : NCX_Reference.zero b=ok true := by
  classical
  have good : NCV_ZeroRun.AllZero b 0 := by
    intro j _ hj
    have bound : j<n := by simpa only [h,List.length_replicate] using hj
    simp only [NCV_ZeroStep.byte,h,List.getElem?_replicate,if_pos bound,Option.getD_some]
  rw [NCX_FieldLaws.zero b (by simpa only [h,List.length_replicate] using cap)]
  simp only [good,decide_true]
theorem nonzero (b : Slice U8) (cap : b.val.length ≤ 768)
    (first : NCV_ZeroStep.byte b 0 ≠ 0#u8) (len : 0<b.val.length) :
    NCX_Reference.zero b=ok false := by
  classical
  have bad : ¬NCV_ZeroRun.AllZero b 0 := by intro h;exact first (h 0 (by omega) len)
  rw [NCX_FieldLaws.zero b cap]
  simp only [bad,decide_false]
theorem magic (b : Slice U8) (m : Array U8 4#usize)
    (fit : 4 ≤ b.val.length) (field : b.val.take 4=m.val) :
    NCX_Reference.magic b m=ok true := by
  have read:=NCV_FieldViews.read_prefix b 4#usize fit
  have eq : NCX_Reference.equal (JHg_FieldRead.segment b 0 4) m.to_slice=ok true := by
    rw [NCX_FieldLaws.equal _ _ (by rw [JHg_FieldRead.length _ 0 4 (by omega)];omega)]
    have h : (JHg_FieldRead.segment b 0 4).val=m.to_slice.val := by
      simpa only [JHg_FieldRead.segment,List.drop_zero,Array.to_slice] using field
    simp only [h,decide_true]
  simpa only [NCX_Reference.magic,read,lift,bind_tc_ok,show (4#usize).val=4 from rfl] using eq

#print axioms zero
#print axioms nonzero
#print axioms magic
end NCX_ZeroLaws
