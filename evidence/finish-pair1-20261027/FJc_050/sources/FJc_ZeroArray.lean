import FIo_GroupCanonical
import FIp_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_ZeroArray
open Aeneas Aeneas.Std
open FIo_FieldBridge (NE)

theorem value (N : Usize) (j : Nat) :
    FIp_ArrayValue.value (Array.repeat N FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO) j=0 := by
  simp only [FIp_ArrayValue.value,Array.repeat,List.getElem?_replicate]
  split <;> first | exact FIo_Constants.zero.2 | rfl
#print axioms value
end AspisR1.FJc_ZeroArray
end
