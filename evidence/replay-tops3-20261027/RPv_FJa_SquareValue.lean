import RPv_FJa_SquareMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_SquareValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (K Canon decode)
/-- Exact native optimized square, reusing the checked word/tower proof. -/
theorem value (x out : NQ) (hx : Canon x) (run : field.QM31.square x=ok out) :
    Canon out ∧ decode out=decode x*decode x := by
  obtain ⟨z,hz,hc,hv⟩ := ExtractedMaskQM31SquareExact.current_qm_square_exact (qm x) hx
  have same := FJa_SquareMap.qm_square x
  rw [run,FIv_Map.map_ok,hz] at same
  have eq := Result.ok.inj same
  rw [←eq] at hc hv
  exact ⟨hc,hv⟩
#print axioms value
end AspisR1.FJa_SquareValue
end
