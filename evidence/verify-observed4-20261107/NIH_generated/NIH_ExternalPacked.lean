import NIH_LocalPacked
import NDO_JGj_ExternalPackedTotal
import RPv_FJe_ExternalPackedValue
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_ExternalPacked
open FIv_NativeArithmetic (NQ)
/-- Complete emitted group/primitive-add/map composition on the SAME canonical input. -/
theorem result (s : Array NQ 16#usize) (canonical : FIw_ArrayValue.canonical s) :
 ∃ out, FIq_Native.state_only_poseidon.external_linear_packed s=ok out ∧
 FIw_ArrayValue.canonical out ∧
 FIw_ArrayValue.decoded out=fun g=>R0P.poseidonPackingFormula
  ExtractedMaskQmPackBase4Arithmetic.iBasis ExtractedMaskQmPackBase4Arithmetic.uBasis
  (fun j=>R0P.poseidonExternalLinear (FIw_ArrayValue.decoded s) (FJe_ExternalAdjoint.lane g j)) := by
 obtain ⟨out,run,_⟩:=JGj_ExternalPackedTotal.source s canonical
 exact ⟨out,run,FJe_ExternalPackedValue.value s out canonical run⟩
#print axioms result
end AspisR1.NIH_ExternalPacked
end
