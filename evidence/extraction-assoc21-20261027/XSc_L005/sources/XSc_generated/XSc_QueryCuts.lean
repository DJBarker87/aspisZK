import XSc_AccumulateCuts
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XSc_QueryCuts
/-- Actual accepted query provenance, through the same geometry, fold and
pending-accumulation call. Canonical arithmetic and raw-row phase are not assumed
or asserted by this cut theorem. -/
theorem source (proof : Slice U8) (p : verifier.Prepared)
 (a out : verifier.Accumulator) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
 (pending after : verifier.BatchedWeights)
 (run : verifier.candidate.query_values proof p a g obs geometry pending=ok (.Ok (out,after))) :
 ∃ (node : aspis_core.field.M31) (folded : aspis_core.field.wide_exact.WideExact),
 verifier.accumulate_batched_with_node p a node folded pending=ok (out,after) ∧
 (a.next+1#usize : Result Usize)=ok out.next ∧ out.weights=a.weights := by
 unfold verifier.candidate.query_values at run
 obtain ⟨i,_,run⟩ := bind_success _ _ _ run
 obtain ⟨u,_,run⟩ := bind_success _ _ _ run
 obtain ⟨q,_,run⟩ := bind_success _ _ _ run
 obtain ⟨dots,_,run⟩ := bind_success _ _ _ run
 obtain ⟨i1,_,run⟩ := bind_success _ _ _ run
 obtain ⟨we,_,run⟩ := bind_success _ _ _ run
 obtain ⟨_,_,run⟩ := bind_success _ _ _ run
 obtain ⟨i2,_,run⟩ := bind_success _ _ _ run
 obtain ⟨we1,_,run⟩ := bind_success _ _ _ run
 obtain ⟨_,_,run⟩ := bind_success _ _ _ run
 obtain ⟨i3,_,run⟩ := bind_success _ _ _ run
 obtain ⟨we2,_,run⟩ := bind_success _ _ _ run
 obtain ⟨_,_,run⟩ := bind_success _ _ _ run
 obtain ⟨i4,_,run⟩ := bind_success _ _ _ run
 obtain ⟨we3,_,run⟩ := bind_success _ _ _ run
 obtain ⟨_,_,run⟩ := bind_success _ _ _ run
 obtain ⟨inverse,_,run⟩ := bind_success _ _ _ run
 obtain ⟨alpha,_,run⟩ := bind_success _ _ _ run
 obtain ⟨folded0,_,run⟩ := bind_success _ _ _ run
 obtain ⟨i5,_,run⟩ := bind_success _ _ _ run
 obtain ⟨_,_,run⟩ := bind_success _ _ _ run
 obtain ⟨values,_,run⟩ := bind_success _ _ _ run
 obtain ⟨i6,_,run⟩ := bind_success _ _ _ run
 obtain ⟨we5,_,run⟩ := bind_success _ _ _ run
 obtain ⟨b,_,run⟩ := bind_success _ _ _ run
 split at run
 · cases run
 · obtain ⟨alpha1,_,run⟩ := bind_success _ _ _ run
   obtain ⟨folded,_,run⟩ := bind_success _ _ _ run
   obtain ⟨i7,_,run⟩ := bind_success _ _ _ run
   obtain ⟨_,_,run⟩ := bind_success _ _ _ run
   obtain ⟨i8,_,run⟩ := bind_success _ _ _ run
   obtain ⟨z,_,run⟩ := bind_success _ _ _ run
   obtain ⟨m,_,run⟩ := bind_success _ _ _ run
   obtain ⟨m1,_,run⟩ := bind_success _ _ _ run
   obtain ⟨m2,_,run⟩ := bind_success _ _ _ run
   obtain ⟨node,_,run⟩ := bind_success _ _ _ run
   obtain ⟨a1,pending1,hacc,run⟩ := pair_bind_success _ _ _ run
   obtain ⟨_,_,run⟩ := bind_success _ _ _ run
   have same := core.result.Result.Ok.inj (Result.ok.inj run)
   cases same
   obtain ⟨one,basis,rows,_,_,_,_,hn,hw,_⟩ := XSc_AccumulateCuts.source p a out node folded pending after hacc
   exact ⟨node,folded,hacc,hn,hw⟩
#print axioms source
end XSc_QueryCuts
