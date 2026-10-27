import XRs_QueryScan
import Query31ModelScanCall
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRt_QueryScan
open Query31ExplicitListLoop Query31ExplicitScanBody

theorem same_scan (xs : List U32) (s : Query31ExplicitScanBody.CurrentScan) (valid : validState s) :
 ∃ sf pending,
 scanListLoop xs s = ok (sf,pending) ∧
 XRs_QueryScan.observe
  (xs.foldl XRn_Join_scanWord (s.accepted.val.take s.accepted_len.val,s.draws.val,false)) =
   (q22StateOf sf,optionStop pending) ∧ validState sf := by
 obtain ⟨sf,pending,run,scan,valid'⟩ := scanListLoop_q22_valid xs s valid
 refine ⟨sf,pending,run,?_,valid'⟩
 rw [XRs_QueryScan.scan]
 exact scan

theorem same_default (xs : List U32) :
 ∃ sf pending,
 scanListLoop xs Query31ConcreteDriverTraceFacts.sourceDefaultState = ok (sf,pending) ∧
 XRs_QueryScan.observe (xs.foldl XRn_Join_scanWord ([],0,false)) =
   (q22StateOf sf,optionStop pending) ∧ validState sf := by
 exact same_scan xs Query31ConcreteDriverTraceFacts.sourceDefaultState
  Query31ConcreteDriverTraceFacts.sourceDefaultState_valid

#print axioms same_default
#print axioms same_scan
end XRt_QueryScan
