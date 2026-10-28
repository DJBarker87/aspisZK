import NBF_LoopFrame
import Port3_NativeQueryTerms
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBF_QueryCuts
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
open Port3_PushFrame (bind_success)
private theorem guard {T : Type} (bad : Bool)
 (tail : Result (core.result.Result T verifier.Error)) (out : T)
 (h : (if bad then ok (.Err verifier.Error.Query) else tail)=ok (.Ok out)) :
 tail=ok (.Ok out) := by cases bad <;> simp_all
/-- Exact opening, dots, inverse, circle/line folds and accumulation cut
from ONE successful direct-cohort query. No independent child is selected. -/
theorem accepted (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a out : verifier.Accumulator) (g : Array Stage2E 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
 (b bout : verifier.BatchedWeights)
 (h : verifier.candidate.query_values ops proof p a g obs geometry b=ok (.Ok (out,bout))) :
 ∃ query opening dots inverse circle values line node,
   Array.index_usize p.queries a.next=ok query ∧
   ops.op11 proof a.next=ok opening ∧ ops.op20 opening g=ok dots ∧
   ops.op18 geometry a.next=ok inverse ∧
   ops.op17 (p.alpha.val[0]'(by have:=p.alpha.property;omega)) dots inverse=ok circle ∧
   ops.op16 (p.alpha.val[1]'(by have:=p.alpha.property;omega)) values inverse=ok line ∧
   verifier.accumulate_batched_with_node ops p a node line b=ok (out,bout) := by
 unfold verifier.candidate.query_values at h
 obtain ⟨query,hquery,h⟩ := bind_success _ _ _ h
 obtain ⟨u,hu,h⟩ := bind_success _ _ _ h
 obtain ⟨opening,hopening,h⟩ := bind_success _ _ _ h
 obtain ⟨dots,hdots,h⟩ := bind_success _ _ _ h
 iterate 15 obtain ⟨x,hx,h⟩ := bind_success _ _ _ h
 obtain ⟨inverse,hinverse,h⟩ := bind_success _ _ _ h
 obtain ⟨alpha0,ha0,h⟩ := bind_success _ _ _ h
 obtain ⟨circle,hcircle,h⟩ := bind_success _ _ _ h
 obtain ⟨i,hi,h⟩ := bind_success _ _ _ h
 obtain ⟨tr,ht,h⟩ := bind_success _ _ _ h
 obtain ⟨values,hvalues,h⟩ := bind_success _ _ _ h
 obtain ⟨idx,hidx,h⟩ := bind_success _ _ _ h
 obtain ⟨selected,hselected,h⟩ := bind_success _ _ _ h
 obtain ⟨bad,hbad,h⟩ := bind_success _ _ _ h
 have h := guard _ _ _ h
 obtain ⟨alpha1,ha1,h⟩ := bind_success _ _ _ h
 obtain ⟨line,hline,h⟩ := bind_success _ _ _ h
 iterate 8 obtain ⟨x,hx,h⟩ := bind_success _ _ _ h
 obtain ⟨node,hnode,h⟩ := bind_success _ _ _ h
 obtain ⟨pair,haccum,h⟩ := bind_success _ _ _ h
 rcases pair with ⟨a1,b1⟩
 obtain ⟨marked,hmark,h⟩ := bind_success _ _ _ h
 cases Result.ok.inj h
 have e0 : alpha0=p.alpha.val[0]'(by have:=p.alpha.property;omega) := by
   simpa [Array.index_usize] using ha0.symm
 have e1 : alpha1=p.alpha.val[1]'(by have:=p.alpha.property;omega) := by
   simpa [Array.index_usize] using ha1.symm
 subst alpha0;subst alpha1
 exact ⟨query,opening,dots,inverse,circle,values,line,node,
   hquery,hopening,hdots,hinverse,hcircle,hline,haccum⟩
#print axioms guard
#print axioms accepted
end NBF_QueryCuts
