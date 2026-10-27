import RPu_FIx_SquareMap
import ExtractedMaskQM31SquareExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_SquareValue
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (K Canon decode)

theorem value (x out : NQ) (hx : Canon x)
    (run : FIq_Native.field.QM31.square x=ok out) :
    Canon out ∧ decode out=decode x*decode x := by
  obtain ⟨z,hz,hc,hv⟩ := ExtractedMaskQM31SquareExact.current_qm_square_exact (qm x) hx
  have mapped := FIx_SquareMap.mapped x
  rw [run,FIv_Map.map_ok,hz] at mapped
  have same := Result.ok.inj mapped
  refine ⟨?_,?_⟩
  · change ExtractedMaskQM31Exact.CurrentCanonicalQM (qm out)
    rw [same]
    exact hc
  · change ExtractedMaskQM31Exact.decode (qm out)=_
    rw [same]
    exact hv
#print axioms value
end AspisR1.FIx_SquareValue
end
