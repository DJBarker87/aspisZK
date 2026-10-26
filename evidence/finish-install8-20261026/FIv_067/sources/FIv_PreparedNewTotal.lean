import FIv_Arithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_PreparedNewTotal
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic
open FIv_NativeValue (Canon)
open FIv_PreparedNew (NP prepared)
open FIv_Map (map map_ok)
theorem value (theta : NQ) (ht : Canon theta) :
    ∃ p : NP, FIq_Native.field.PreparedQm31Multiplier.new theta=ok p ∧
      ExtractedMaskPreparedState.PreparedFor (prepared p) (qm theta) := by
  obtain ⟨p',hp,hvalid⟩ := ExtractedMaskPreparedState.current_prepared_new (qm theta) ht
  have same := FIv_PreparedNew.mapped theta
  rw [hp] at same
  cases run : FIq_Native.field.PreparedQm31Multiplier.new theta with
  | fail e => rw [run] at same; cases same
  | div => rw [run] at same; cases same
  | ok p => exact ⟨p,rfl,FIv_PreparedNew.valid theta p ht run⟩
#print axioms value
end AspisR1.FIv_PreparedNewTotal
end
