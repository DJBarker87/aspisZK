import XRv_QueryScanTotal
import XRv_DriverSelected
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRv_PairedStep
open XRv_QueryDriver XRv_QueryDriverTotal
open Query31ExplicitListLoop Query31ExplicitScanBody

theorem same_step (blocks advances : Blocks) (i : Nat) (hi : i<8)
 (s : Query31ExplicitScanBody.CurrentScan) (valid : validState s) (oldState : Block) :
 ∃ sf pending advance,
 Array.index_usize advances (XRn_Join_usize i) = ok advance ∧
 Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords s
   (blocks.val[i]'(by have h : blocks.val.length=8 := blocks.property; omega)) =
     ok (optionStop pending,sf) ∧
 step blocks advances
   (s.accepted.val.take s.accepted_len.val,s.draws.val,false,oldState) i =
     ok (sf.accepted.val.take sf.accepted_len.val,sf.draws.val,optionStop pending,advance) ∧
 validState sf := by
 have hlen : blocks.val.length=8 := blocks.property
 obtain ⟨sf,pending,hr,he,hv⟩ := XRv_QueryScanTotal.same_block (blocks.val[i]'(by omega)) s valid
 refine ⟨sf,pending,advances.val[i]'(by have h : advances.val.length=8 := advances.property; omega),index advances i hi,hr,?_,hv⟩
 unfold step
 simp only [index blocks i hi,index advances i hi,bind_tc_ok]
 rw [he]

#print axioms same_step
end XRv_PairedStep
