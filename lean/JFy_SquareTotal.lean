import JFy_SquareMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_SquareTotal
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic
open FIv_NativeValue (Canon decode)
open FIv_Map (map map_ok)

theorem source (x : NQ) (hx : Canon x) :
    ∃ out,FIq_Native.field.QM31.square x=ok out ∧ Canon out ∧ decode out=decode x*decode x := by
  obtain ⟨z,hz,hc,hv⟩ := ExtractedMaskQM31SquareExact.current_qm_square_exact (qm x) hx
  have same := JFy_SquareMap.source x
  rw [hz] at same
  cases run : FIq_Native.field.QM31.square x with
  | fail e => rw [run] at same;cases same
  | div => rw [run] at same;cases same
  | ok out =>
    rw [run,map_ok] at same
    have eq := Result.ok.inj same
    rw [← eq] at hc hv
    exact ⟨out,rfl,hc,hv⟩
#print axioms source
end AspisR1.JFy_SquareTotal
end
