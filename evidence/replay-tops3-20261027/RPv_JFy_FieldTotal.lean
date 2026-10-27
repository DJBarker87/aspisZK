import RPv_FIv_PreparedTotal
import RPv_FIv_SubMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_FieldTotal
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic
open FIv_NativeValue (Canon decode)
open FIv_Map (map map_ok)

theorem sub (x y : NQ) (hx : Canon x) (hy : Canon y) :
    ∃ out,FIq_Native.field.QM31.sub x y=ok out ∧ Canon out ∧ decode out=decode x-decode y := by
  obtain ⟨z,hz,hc,hv⟩ := EqualityValueAdapter.current_qm_sub_exact (qm x) (qm y) hx hy
  have same := FIv_SubMap.mapped x y
  rw [hz] at same
  cases run : FIq_Native.field.QM31.sub x y with
  | fail e => rw [run] at same;cases same
  | div => rw [run] at same;cases same
  | ok out => exact ⟨out,rfl,FIv_SubMap.qm x y out hx hy run⟩
#print axioms sub

theorem mul (x y : NQ) (hx : Canon x) (hy : Canon y) :
    ∃ out,FIq_Native.field.QM31.mul x y=ok out ∧ Canon out ∧ decode out=decode x*decode y := by
  obtain ⟨z,hz,hc,hv⟩ := ExtractedMaskQM31Exact.current_qm_mul_exact (qm x) (qm y) hx hy
  have same := FIv_NativeQM.mul x y
  rw [hz] at same
  cases run : FIq_Native.field.QM31.mul x y with
  | fail e => rw [run] at same;cases same
  | div => rw [run] at same;cases same
  | ok out => exact ⟨out,rfl,FIv_NativeValue.mul x y out hx hy run⟩
#print axioms mul
end AspisR1.JFy_FieldTotal
end
