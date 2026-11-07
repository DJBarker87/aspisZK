import RSL_Base
set_option autoImplicit false
namespace LIB_DigestGuards
def guarded {A : Type} : List Bool → A → Option A
 | [],v => some v
 | b::bs,v => if b then guarded bs v else none
theorem all {A : Type} (bs : List Bool) (v : A) :
 guarded bs v = if bs.all id then some v else none := by
 induction bs with
 | nil => rfl
 | cons b bs ih => cases b <;> simp [guarded,ih]
#print axioms all
end LIB_DigestGuards
