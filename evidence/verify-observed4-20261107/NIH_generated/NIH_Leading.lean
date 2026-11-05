import NIH_FullRounds
import NDO_JGj_LeadingTotal
import RPv_FJe_LeadingPackedValue
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_Leading
open FIv_NativeArithmetic (NQ)
/-- Actual leading absorption, frozen constants and both rounds on one state. -/
theorem result (o : FJa_PoseidonOrigins.Openings)
 (hz : FIw_ArrayValue.canonical o.z) (hx : FIw_ArrayValue.canonical o.xor12_z) :
 ∃ out,FIq_Native.state_only_poseidon.leading_pair_packed o=ok out ∧
 FIw_ArrayValue.canonical out ∧
 FIw_ArrayValue.decoded out=fun g=>R0P.poseidonPackingFormula
  ExtractedMaskQmPackBase4Arithmetic.iBasis ExtractedMaskQmPackBase4Arithmetic.uBasis
  (fun j=>R0P.poseidonLeadingPair (FIw_ArrayValue.decoded o.z)
   (FIw_ArrayValue.decoded o.xor12_z) (FJe_ExternalAdjoint.lane g j)) := by
 obtain ⟨out,run,_⟩:=JGj_LeadingTotal.source o hz hx
 exact ⟨out,run,FJe_LeadingPackedValue.value o out hz hx run⟩
#print axioms result
end AspisR1.NIH_Leading
end
