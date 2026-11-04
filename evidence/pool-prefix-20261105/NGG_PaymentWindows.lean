import NFD_RequestDomains
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace NGG_PaymentWindows
/-- The216-byte payment child window never includes the four appended hints. -/
theorem point (body : Array U8 320#usize) (suffix : List U8)
    (j : Nat) (bound : j < 216) :
    (((body.val ++ suffix).drop 104).take 216)[j]? = body.val[104+j]? := by
  have length : body.val.length=320 := body.property
  have inside : 104+j < body.val.length := by omega
  have equal : (body.val ++ suffix)[104+j]? = body.val[104+j]? :=
    List.getElem?_append_left inside
  simpa [List.getElem?_take,List.getElem?_drop,bound,Nat.add_comm] using equal
#print axioms point

theorem domain (body : Array U8 320#usize) :
    (body.val.drop 104).length = 216 := NFD_RequestDomains.payment_length body
#print axioms domain
end NGG_PaymentWindows
