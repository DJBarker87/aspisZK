import RPv_FIw_ArrayValue
set_option autoImplicit false
namespace AspisR1.JFy_ZeroArrays
open Aeneas Aeneas.Std FIq_Native

theorem source (N : Usize) : FIw_ArrayValue.canonical (Array.repeat N field.QM31.ZERO) := by
  intro x hx
  have same : x=field.QM31.ZERO := List.eq_of_mem_replicate hx
  exact same ▸ FIv_NativeValue.zero.1
#print axioms source
end AspisR1.JFy_ZeroArrays
