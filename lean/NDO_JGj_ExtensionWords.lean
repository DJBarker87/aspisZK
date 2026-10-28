import NDO_JGj_RawBounds
set_option autoImplicit false
namespace AspisR1.JGj_ExtensionWords
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
theorem canonical (x : NQ) (hx : FIv_NativeValue.Canon x) :
    JGj_RawBounds.Canonical (FJb_LimbMap.words x) := by
  intro j
  fin_cases j
  · exact hx.1.1
  · exact hx.1.2
  · exact hx.2.1
  · exact hx.2.2
#print axioms canonical
end AspisR1.JGj_ExtensionWords
