import NGG_LayoutGTransfer
import NGG_LayoutGWithdrawal
import NGG_LayoutRTransfer
import NGG_LayoutRWithdrawal
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGG_LayoutValue
open NGG_SpineRef
theorem result (rollover withdrawal : Bool) (n : Usize)
    (unique : core.result.Result Unit NGGSpineError) :
    NGG_SpineRef.layout_tail (cursor rollover) withdrawal n unique =
      ok (value rollover withdrawal n unique) := by
  cases rollover <;> cases withdrawal
  · exact NGG_LayoutGTransfer.result n unique
  · exact NGG_LayoutGWithdrawal.result n unique
  · exact NGG_LayoutRTransfer.result n unique
  · exact NGG_LayoutRWithdrawal.result n unique
#print axioms result
end NGG_LayoutValue
