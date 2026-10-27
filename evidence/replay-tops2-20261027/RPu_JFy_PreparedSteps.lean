import RPu_JFy_Steps
import RPu_FIv_PreparedNewTotal
import RPu_FIw_ScalarArithmetic
import RPu_FIx_ArithmeticTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_PreparedSteps
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIv_NativeArithmetic (NQ qm)
open FIv_PreparedNew (NP prepared)

def Valid (p : NP) := ∃ theta : NQ,Canon theta ∧ ExtractedMaskPreparedState.PreparedFor (prepared p) (qm theta)
@[step] theorem new (theta : NQ) (ht : Canon theta) : field.PreparedQm31Multiplier.new theta ⦃ out => Valid out ⦄ := by
  obtain ⟨p,call,hp⟩ := FIv_PreparedNewTotal.value theta ht
  rw [call]
  exact ⟨theta,ht,hp⟩
#print axioms new
@[step] theorem mul (p : NP) (x : NQ) (hp : Valid p) (hx : Canon x) :
    field.PreparedQm31Multiplier.mul p x ⦃ out => Canon out ⦄ := by
  obtain ⟨theta,ht,hp⟩ := hp
  obtain ⟨out,call,hout,_⟩ := FIv_PreparedTotal.mul p theta x ht hx hp
  rw [call]
  exact hout
#print axioms mul
@[step] theorem scalar (x : NQ) (s : U32) : field.QM31.mul_m31 x s ⦃ out => Canon out ⦄ := by
  obtain ⟨out,call,hc,_⟩ := ExtractedMaskScalarExact.current_qm_mul_m31_exact (qm x) s
  obtain ⟨native,hn,_⟩ := FIx_ArithmeticTotal.map_success qm _ out ((FIw_ScalarArithmetic.qm_mapped x s).trans call)
  rw [hn]
  exact (FIw_ScalarArithmetic.mul x native s hn).1
#print axioms scalar
end AspisR1.JFy_PreparedSteps
end
