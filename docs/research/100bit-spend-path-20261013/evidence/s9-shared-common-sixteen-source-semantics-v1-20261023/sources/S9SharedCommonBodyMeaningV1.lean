import S9SharedCommonBodyTraceV1
import S9ActualTensorStoredProductV1
import S9ConstructorNativeReceiverCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9SharedCommonBodyMeaningV1
open AspisR1S9SharedCommonBodyTraceV1
open AspisR1S9ActualTensorArithmeticV1
open AspisR1S9ActualTensorStoredProductV1
abbrev Can := AspisR1S9ActualPairQMHelperTransportV1.Canonical
abbrev FactorsCanonical := AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical

def expectedBits (self : weights.Weights) (j : Usize) : ExactQM :=
  storedFactor self 0#usize 2 (j &&& 3#usize).val *
    storedFactor self 0#usize 3 (Usize.wrapping_shr j 2#u32).val

/-- Same successful source continuation supplies both multiplication inputs,
output, and mutable write. No initial common-array meaning is required. -/
theorem actual_body_cont_meaning (self : weights.Weights) (iter iterNext : R)
    (common commonNext : Common) (hcan : FactorsCanonical self)
    (h : weights.Weights.pair_loop1.body self iter common=.ok (.cont (iterNext,commonNext))) :
    ∃ (j : Usize) (product : Q),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some j,iterNext) ∧
      Array.update common j product=.ok commonNext ∧ Can product ∧
      decode product=expectedBits self j := by
  rcases actual_body_success_trace self iter common _ h with hd | hc
  · rcases hd with ⟨it,hn,he⟩
    cases he
  · rcases hc with ⟨j,it,row,c2,c3,q2,q3,product,next,
        hn,hr,hc2,hq2,hc3,hq3,hm,hu,he⟩
    have ep : (iterNext,commonNext)=(it,next) := ControlFlow.cont.inj he
    cases ep
    have h2 : Can q2 := hcan 0#usize 2#usize row c2 (j &&& 3#usize) q2 hr hc2 hq2
    have h3 : Can q3 := hcan 0#usize 3#usize row c3 (Usize.wrapping_shr j 2#u32) q3 hr hc3 hq3
    obtain ⟨hp,hprod⟩ := native_mul_success_exact q2 q3 product h2 h3 hm
    have e2 := stored_factor_read self 0#usize 2#usize (j &&& 3#usize) row c2 q2 hr hc2 hq2
    have e3 := stored_factor_read self 0#usize 3#usize (Usize.wrapping_shr j 2#u32) row c3 q3 hr hc3 hq3
    refine ⟨j,product,hn,hu,hp,?_⟩
    unfold expectedBits
    change storedFactor self 0#usize 2 (j &&& 3#usize).val=decode q2 at e2
    change storedFactor self 0#usize 3 (Usize.wrapping_shr j 2#u32).val=decode q3 at e3
    rw [e2,e3]
    exact hprod

theorem actual_body_done (self : weights.Weights) (iter : R) (common : Common)
    (out : Output) (h : weights.Weights.pair_loop1.body self iter common=.ok (.done out)) :
    out=(self,common) ∧ ∃ it,
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (none,it) := by
  rcases actual_body_success_trace self iter common _ h with hd | hc
  · rcases hd with ⟨it,hn,he⟩
    exact ⟨ControlFlow.done.inj he, it, hn⟩
  · rcases hc with ⟨j,it,row,c2,c3,q2,q3,product,next,
        hn,hr,hc2,hq2,hc3,hq3,hm,hu,he⟩
    cases he

#print axioms actual_body_cont_meaning
#print axioms actual_body_done
end AspisR1S9SharedCommonBodyMeaningV1
