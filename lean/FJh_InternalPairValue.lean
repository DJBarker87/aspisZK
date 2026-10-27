import FJh_InternalRoundValue
import FJh_InternalPairOrigins
import FJh_InternalDotValue
import FJh_InternalConstantCalls
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_InternalPairValue
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (State QM Decode cell)
open FIw_ArrayValue (canonical decoded)
/-- Complete actual internal-pair VALUE on the SAME selector interpolation. -/
theorem value (s l out : State) (hs : canonical s) (hl : canonical l)
    (run : state_only_poseidon.interpolated_internal_pair s l=ok out) :
    canonical out ∧ decoded out=R0P.poseidonInterpolatedInternalPair (decoded s) (decoded l) := by
  obtain ⟨w,e,o,even,odd,mid,rw,re,ro,reven,rodd,rm,rf⟩ := FJh_InternalPairOrigins.reached s l out run
  have vw := FJh_InternalWeights.value l w hl rw
  have ve := FJh_InternalDotValue.value w e even vw.1 (by
    intro i
    rw [FJh_InternalConstantCalls.even_value e re i]
    exact FJh_InternalConstants.canonical _) reven
  have vo := FJh_InternalDotValue.value w o odd vw.1 (by
    intro i
    rw [FJh_InternalConstantCalls.odd_value o ro i]
    exact FJh_InternalConstants.canonical _) rodd
  have vm := FJh_InternalRoundValue.value s mid even hs ve.1 rm
  have vf := FJh_InternalRoundValue.value mid out odd vm.1 vo.1 rf
  refine ⟨vf.1,?_⟩
  rw [vf.2,vm.2,ve.2,vo.2]
  simp_rw [vw.2,FJh_InternalConstantCalls.even_value e re,
    FJh_InternalConstantCalls.odd_value o ro,FJh_InternalConstants.model]
  rfl
#print axioms value
end AspisR1.FJh_InternalPairValue
end
