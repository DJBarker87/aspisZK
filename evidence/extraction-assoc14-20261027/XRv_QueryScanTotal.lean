import XRv_DecodedWords
import XRt_QueryScan
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRv_QueryScanTotal
open Query31ExplicitListLoop Query31ExplicitScanBody

theorem values_injective (xs ys : List U32) (h : xs.map UScalar.val = ys.map UScalar.val) : xs = ys := by
 induction xs generalizing ys with
 | nil => cases ys <;> simp_all
 | cons x xs ih =>
   cases ys with
   | nil => simp at h
   | cons y ys =>
     have hp := List.cons.inj h
     have he : x=y := UScalar.eq_of_val_eq hp.1
     exact congrArg₂ List.cons he (ih ys hp.2)

theorem observe_injective (x y : List U32 × Nat × Bool)
 (h : XRs_QueryScan.observe x = XRs_QueryScan.observe y) : x = y := by
 rcases x with ⟨xs,xd,xb⟩
 rcases y with ⟨ys,yd,yb⟩
 have hp := congrArg (fun p => p.1.accepted) h
 have hd := congrArg (fun p => p.1.draws) h
 have hb := congrArg Prod.snd h
 have he := values_injective xs ys hp
 exact congrArg₂ Prod.mk he (congrArg₂ Prod.mk hd hb)

theorem same_block (b : Array U8 32#usize) (s : CurrentScan) (valid : validState s) :
 ∃ sf pending,
 Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords s b =
   ok (optionStop pending,sf) ∧
 (XRt_QueryWords.words b).foldl XRn_Join_scanWord
   (s.accepted.val.take s.accepted_len.val,s.draws.val,false) =
   (sf.accepted.val.take sf.accepted_len.val,sf.draws.val,optionStop pending) ∧
 validState sf := by
 obtain ⟨sf,pending,hr,ho,hv⟩ := XRt_QueryScan.same_scan (XRt_QueryWords.words b) s valid
 refine ⟨sf,pending,?_,?_,hv⟩
 · unfold Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords
   rw [XRv_DecodedWords.exact_result,bind_tc_ok]
   change (do let (sf,p) ← scanListLoop (XRt_QueryWords.words b) s; ok (optionStop p,sf)) = _
   rw [hr,bind_tc_ok]
 · apply observe_injective
   exact ho

#print axioms values_injective
#print axioms observe_injective
#print axioms same_block
end XRv_QueryScanTotal
