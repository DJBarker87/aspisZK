import RPu_FIo_GroupCanonical
import RPu_FIp_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_ZeroArray
open Aeneas Aeneas.Std
open FIo_FieldBridge (NE)

theorem value (N : Usize) (j : Nat) :
    FIp_ArrayValue.value (Array.repeat N FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO) j=0 := by
  by_cases h : j<N.val
  · simp only [FIp_ArrayValue.value,Array.repeat,List.getElem?_replicate,if_pos h,FIo_Constants.zero.2]
  · simp only [FIp_ArrayValue.value,Array.repeat,List.getElem?_replicate,if_neg h]
#print axioms value
end AspisR1.FJc_ZeroArray
end
