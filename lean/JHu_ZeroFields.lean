import NCV_ZeroRun
import NCV_EqualValue
set_option autoImplicit false
namespace AspisR1.JHu_ZeroFields
open Aeneas Aeneas.Std Result

theorem zero (b : Slice U8) (n : Nat) (h : b.val=List.replicate n 0#u8)
    (cap : n ≤ 768) : NCV_Reference.zero b=ok true := by
  classical
  have good : NCV_ZeroRun.AllZero b 0 := by
    intro j _ hj
    have bound : j<n := by simpa only [h,List.length_replicate] using hj
    simp only [NCV_ZeroStep.byte,h,List.getElem?_replicate,if_pos bound,Option.getD_some]
  rw [NCV_ZeroRun.value b (by simpa only [h,List.length_replicate] using cap)]
  simp only [good,decide_true]
#print axioms zero

theorem nonzero (b : Slice U8) (cap : b.val.length ≤ 768)
    (first : NCV_ZeroStep.byte b 0 ≠ 0#u8) (len : 0<b.val.length) :
    NCV_Reference.zero b=ok false := by
  classical
  have bad : ¬NCV_ZeroRun.AllZero b 0 := by intro h;exact first (h 0 (by omega) len)
  rw [NCV_ZeroRun.value b cap]
  simp only [bad,decide_false]
#print axioms nonzero

theorem equal (b v : Slice U8) (cap : b.val.length ≤ 768) (h : b.val=v.val) :
    NCV_Reference.equal b v=ok true := by
  classical
  rw [NCV_EqualValue.value b v cap]
  simp only [h,decide_true]
#print axioms equal
end AspisR1.JHu_ZeroFields
