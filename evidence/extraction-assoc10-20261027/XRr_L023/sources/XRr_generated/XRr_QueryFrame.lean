import XRr_AccumulateFrame
import XRr_QueryRead
import CurrentCallerUsizeArithmeticV1
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XRr_QueryFrame
theorem accumulate (p : verifier.Prepared) (a out : verifier.Accumulator)
 (node : aspis_core.field.M31) (value : aspis_core.field.wide_exact.WideExact)
 (b bout : verifier.BatchedWeights) (bound : a.next.val<22)
 (h : verifier.accumulate_batched_with_node p a node value b=ok (out,bout)) :
 out.weights=a.weights ∧ out.next.val=a.next.val+1 := by
 have hw := XRr_AccumulateFrame.weights p a out node value b bout h
 unfold verifier.accumulate_batched_with_node at h
 iterate 10 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
 obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
 have hp := Result.ok.inj h
 cases hp
 refine ⟨hw,?_⟩
 have spec := WP.spec_imp_exists (UScalar.add_spec a.next 1#usize (by scalar_tac))
 obtain ⟨x,hx,hval⟩ := spec
 have he : x=next := Result.ok.inj (hx.symm.trans hn)
 simpa only [he] using hval
private theorem guard {T : Type} (b : Bool)
 (tail : Result (core.result.Result T verifier.Error)) (out : T)
 (h : (if b then ok (.Err verifier.Error.Query) else tail)=ok (.Ok out)) :
 tail=ok (.Ok out) := by cases b <;> first | exact h | cases h
/-- All calls are cuts of this actual query, including its node and row update. -/
theorem query (proof : Slice U8) (p : verifier.Prepared)
 (a out : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (b bout : verifier.BatchedWeights)
 (h : verifier.candidate.query_values proof p a g obs geo b=ok (.Ok (out,bout))) :
 a.next.val<22 ∧ out.weights=a.weights ∧ out.next.val=a.next.val+1 := by
 unfold verifier.candidate.query_values at h
 obtain ⟨word,read,h⟩ := bind_success _ _ _ h
 have hb := XRr_QueryRead.bound p a word read
 iterate 27 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
 have h := guard _ _ _ h
 iterate 11 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
 obtain ⟨pair,hacc,h⟩ := bind_success _ _ _ h
 rcases pair with ⟨a1,b1⟩
 obtain ⟨marked,_,h⟩ := bind_success _ _ _ h
 cases Result.ok.inj h
 exact ⟨hb,accumulate p a out _ _ b bout hb hacc⟩
#print axioms accumulate
#print axioms guard
#print axioms query
end XRr_QueryFrame
