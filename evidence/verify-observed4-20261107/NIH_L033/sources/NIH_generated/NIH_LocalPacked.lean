import NIH_PackedBounds
import FJe_LocalPackedValue
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_LocalPacked
open FIv_NativeArithmetic (NQ)
/-- Total SAME-call composition; neither a raw reply nor a success is assumed. -/
theorem result (input : Array NQ 4#usize) (canonical : FIw_ArrayValue.canonical input) :
 ∃ out, FIq_Native.state_only_poseidon.external_local_packed input=ok out ∧
 FIv_NativeValue.Canon out ∧
 FIv_NativeValue.decode out=R0P.poseidonPackingFormula
  ExtractedMaskQmPackBase4Arithmetic.iBasis ExtractedMaskQmPackBase4Arithmetic.uBasis
  (R0P.poseidonMat4 (FIw_ArrayValue.decoded input)) := by
 obtain ⟨raw,run,_⟩:=NIH_PackedBounds.raw input canonical
 obtain ⟨a,b,c,d,reduce,_,_,_,_,_,_,_,_⟩:=NIH_RawExtension.result raw
 have full : FIq_Native.state_only_poseidon.external_local_packed input=ok ⟨⟨a,b⟩,⟨c,d⟩⟩ := by
  simp only [FIq_Native.state_only_poseidon.external_local_packed,run,bind_tc_ok,reduce]
 exact ⟨_,full,FJe_LocalPackedValue.value input _ canonical full⟩
#print axioms result
end AspisR1.NIH_LocalPacked
end
