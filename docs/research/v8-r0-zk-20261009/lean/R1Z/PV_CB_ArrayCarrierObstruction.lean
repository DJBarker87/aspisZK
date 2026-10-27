import R1Z.PDict_CryptoTypesSource
import R1Z.ProverRwSuccessArithmeticTotal
set_option autoImplicit false
namespace R1Z.PV_CB_ArrayCarrierObstruction
open Aeneas Aeneas.Std Result ProverRwSuccessArithmeticTotal
/-- Model obstruction only: Rust's unsafe ArrayLength representation invariant
is not inferred for arbitrary associated carrier types in the Lean signature. -/
theorem no_array (T N : Type) :
    ¬ Nonempty (PDict_CryptoTypes.generic_array.GenericArray T N Empty) := by
  rintro ⟨array⟩
  exact Empty.elim array.data
theorem no_array_total (T N : Type)
    (r : Result (PDict_CryptoTypes.generic_array.GenericArray T N Empty)) : ¬ Total r := by
  rintro ⟨array,h⟩
  exact Empty.elim array.data
theorem no_wrapper_total (T Kind N Bound : Type)
    (r : Result (PDict_CryptoTypes.digest.core_api.wrapper.CoreWrapper T Kind N Empty Bound)) :
    ¬ Total r := by
  rintro ⟨wrapper,h⟩
  exact Empty.elim wrapper.buffer.buffer.data
#print axioms no_array
#print axioms no_array_total
#print axioms no_wrapper_total
end R1Z.PV_CB_ArrayCarrierObstruction
