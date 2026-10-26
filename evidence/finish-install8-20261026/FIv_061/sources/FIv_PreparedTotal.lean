import FIv_PreparedMul
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_PreparedTotal
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic
open FIv_NativeValue (Canon decode K)
open FIv_PreparedNew (NP prepared)
open FIv_Map (map map_ok)
theorem mul (p : NP) (theta x : NQ) (ht : Canon theta) (hx : Canon x)
    (hp : ExtractedMaskPreparedState.PreparedFor (prepared p) (qm theta)) :
    ∃ out, FIq_Native.field.PreparedQm31Multiplier.mul p x=ok out ∧
      Canon out ∧ decode out=decode theta*decode x := by
  obtain ⟨z,hz,hc,hv⟩ := ExtractedMaskPreparedMul.prepared_mul_exact (prepared p) (qm theta) (qm x) ht hx hp
  have same := FIv_PreparedMul.mapped p x
  rw [hz] at same
  cases run : FIq_Native.field.PreparedQm31Multiplier.mul p x with
  | fail e => rw [run] at same; cases same
  | div => rw [run] at same; cases same
  | ok out => exact ⟨out,rfl,FIv_PreparedMul.value p theta x out ht hx hp run⟩

theorem add (x y : NQ) (hx : Canon x) (hy : Canon y) :
    ∃ out, FIq_Native.field.QM31.add x y=ok out ∧ Canon out ∧ decode out=decode x+decode y := by
  obtain ⟨z,hz,hc,hv⟩ := ExtractedMaskQM31Exact.current_qm_add_exact (qm x) (qm y) hx hy
  have same := FIv_NativeQM.add x y
  rw [hz] at same
  cases run : FIq_Native.field.QM31.add x y with
  | fail e => rw [run] at same; cases same
  | div => rw [run] at same; cases same
  | ok out => exact ⟨out,rfl,FIv_NativeValue.add x y out hx hy run⟩
#print axioms mul
#print axioms add
end AspisR1.FIv_PreparedTotal
end
