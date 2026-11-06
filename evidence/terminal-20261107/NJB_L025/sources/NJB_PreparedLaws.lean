import NJB_StubLaws
import NFQ_PreparedMultiplier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_PreparedLaws
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (Canon decode)
open FIv_PreparedNew (NP prepared)
abbrev Domain (p : NP) (theta : NQ) : Prop :=
 ExtractedMaskPreparedState.PreparedFor (prepared p) (qm theta)
/-- The SAME canonical multiplier establishes the prepared-call domain; no
prepared-cache correctness premise is introduced at a caller. -/
theorem new_result (theta : NQ) (canonical : Canon theta) :
 ∃ p,FIq_Native.field.PreparedQm31Multiplier.new theta=ok p ∧ Domain p theta := by
 obtain ⟨probe,call,_⟩ := NFQ_PreparedMultiplier.source (qm theta) canonical
 have mapped := FIv_PreparedNew.mapped theta
 rw [call] at mapped
 cases run : FIq_Native.field.PreparedQm31Multiplier.new theta with
 | fail e => rw [run] at mapped;cases mapped
 | div => rw [run] at mapped;cases mapped
 | ok p => exact ⟨p,rfl,FIv_PreparedNew.valid theta p canonical run⟩
theorem mul_result (p : NP) (theta x : NQ) (ht : Canon theta) (hx : Canon x)
 (domain : Domain p theta) :
 ∃ out,FIq_Native.field.PreparedQm31Multiplier.mul p x=ok out ∧
 Canon out ∧ decode out=decode theta*decode x :=
 FIv_PreparedTotal.mul p theta x ht hx domain
#print new_result
#print mul_result
#print axioms new_result
#print axioms mul_result
end AspisR1.NJB_PreparedLaws
end
