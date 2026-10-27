import LPk_Result
import XRv_QueryScanTotal
import XRv_DriverSelected
import XRt_CohortMultiply
import LPi_TowerValues
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRw_PairedStep
open XRv_QueryDriver XRv_QueryDriverTotal
open Query31ExplicitListLoop Query31ExplicitScanBody

theorem same_step (blocks advances : Blocks) (i : Nat) (hi : i<8)
 (s : Query31ExplicitScanBody.CurrentScan) (valid : validState s) (oldState : Block) :
 ∃ sf pending advance,
 Array.index_usize advances (XRn_Join_usize i) = ok advance ∧
 Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords s
   (blocks.val[i]'(by have h : blocks.val.length=8 := blocks.property; omega)) =
     ok (optionStop pending,sf) ∧
 XRv_QueryDriver.step blocks advances
   (s.accepted.val.take s.accepted_len.val,s.draws.val,false,oldState) i =
     ok (sf.accepted.val.take sf.accepted_len.val,sf.draws.val,optionStop pending,advance) ∧
 validState sf := by
 have hlen : blocks.val.length=8 := blocks.property
 obtain ⟨sf,pending,hr,he,hv⟩ := XRv_QueryScanTotal.same_block (blocks.val[i]'(by omega)) s valid
 refine ⟨sf,pending,advances.val[i]'(by have h : advances.val.length=8 := advances.property; omega),index advances i hi,hr,?_,hv⟩
 unfold XRv_QueryDriver.step
 simp only [index blocks i hi,index advances i hi,bind_tc_ok]
 exact congrArg (fun t : List U32 × Nat × Bool =>
   Result.ok (t.1,t.2.1,t.2.2,advances.val[i]'(by have h : advances.val.length=8 := advances.property; omega))) he

#print axioms same_step
end XRw_PairedStep

#print axioms XRv_FromFnTotal.loop
#print axioms XRv_FromFnTotal.total
#print axioms XRv_DecoderTotal.ranks
#print axioms XRv_DecoderTotal.map_stable
#print axioms XRv_DecoderTotal.decoder
#print axioms XRv_DecodedWords.exact_result
#print axioms XRv_DecodedWords.continuation
#print axioms XRv_DecodedWords.no_failure
#print axioms XRv_DecodedWords.no_divergence
#print axioms XRv_QueryDriver.stopped
#print axioms XRv_QueryDriver.short_circuit
#print axioms XRv_QueryDriver.driver
#print axioms XRv_QueryDriverTotal.index
#print axioms XRv_QueryDriverTotal.step_total
#print axioms XRv_QueryDriverTotal.fold_total
#print axioms XRv_QueryDriverTotal.total
#print axioms XRv_QueryScanTotal.values_injective
#print axioms XRv_QueryScanTotal.observe_injective
#print axioms XRv_QueryScanTotal.same_block
#print axioms XRv_SelectedAdvance.step_selected
#print axioms XRv_SelectedAdvance.fold_selected
#print axioms XRv_DriverSelected.selected
#print axioms LPk_Result.native_result
#print axioms XRq_Nonvacuity.leaf_inhabited
#print axioms XRp_SamplerNonvacuity.both_succeed
