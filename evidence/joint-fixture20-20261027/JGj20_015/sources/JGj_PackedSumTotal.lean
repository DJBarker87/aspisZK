import FJe_ExternalCalls
import JFy_Specs
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_PackedSumTotal
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
theorem source (p : FJe_ExternalCalls.Packed) (hp : canonical p) :
    ∃ total,FJe_ExternalCalls.sum p=ok total ∧ Canon total := by
  have zero : Canon field.QM31.ZERO := FIv_NativeValue.zero.1
  have spec : FJe_ExternalCalls.sum p ⦃ out=>Canon out ⦄ := by
    unfold FJe_ExternalCalls.sum
    step* <;> scalar_tac
  exact WP.spec_imp_exists spec
#print axioms source
end AspisR1.JGj_PackedSumTotal
end
