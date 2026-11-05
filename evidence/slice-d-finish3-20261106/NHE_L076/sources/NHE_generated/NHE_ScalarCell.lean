import NHE_ScalarProductLaw
import NHE_RoundRef
set_option autoImplicit false
namespace NHE_ScalarCell
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

def run (value : NE) (scalar : NQ) (carry : NE) : Result NE := do
 let product ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 value scalar
 FIo_Native.aspis_core.field.wide_exact.WideExact.add carry product

theorem total (value : NE) (scalar : NQ) (carry : NE)
 (hv : canonE value) (hs : canonQ scalar) (hc : canonE carry) :
 ∃ product out,
 FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 value scalar=ok product ∧ canonE product ∧
 run value scalar carry=ok out ∧ canonE out ∧
 NGW_HelperRef.polynomial_step_ref (NGM_RawWords.nativeWords carry) (NGM_RawWords.nativeWords product)=ok (NGM_RawWords.nativeWords out) := by
 obtain ⟨product,hp,cp,_⟩ := NHE_ScalarProductLaw.product value scalar hv hs
 obtain ⟨out,ho,co⟩ := NGW_PolynomialAdd.total carry product hc cp
 have ref := NGW_PolynomialAdd.observed carry product hc cp
 rw [ho] at ref
 exact ⟨product,out,hp,cp,by simp only [run,hp,ho,bind_tc_ok],co,ref⟩

#print axioms total
#print FIo_Native.core.iter.traits.iterator.Iterator.fold.default
end NHE_ScalarCell
