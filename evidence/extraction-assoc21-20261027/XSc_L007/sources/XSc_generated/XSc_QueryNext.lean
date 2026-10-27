import XSc_QueryCuts
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_QueryNext
theorem bound (p : verifier.Prepared) (i : Usize) (q : U32)
 (read : Array.index_usize p.queries i=ok q) : i.val<10 := by
 by_contra h
 have outside : ¬ i.val<p.queries.val.length := by
  have len := p.queries.property
  change p.queries.val.length=10 at len
  omega
 simp only [Array.index_usize] at read
 split at read
 · contradiction
 · cases read
/-- Every actual successful query advances exactly one index and preserves the
same destination weights. This is provenance, not a canonicality assumption. -/
theorem source (proof : Slice U8) (p : verifier.Prepared)
 (a out : verifier.Accumulator) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
 (pending after : verifier.BatchedWeights)
 (run : verifier.candidate.query_values proof p a g obs geometry pending=ok (.Ok (out,after))) :
 a.next.val<10 ∧ out.next.val=a.next.val+1 ∧ out.weights=a.weights := by
 obtain ⟨q,node,folded,hread,_,hnext,hw⟩ := XSc_QueryCuts.source proof p a out g obs geometry pending after run
 have hb := bound p a.next q hread
 have hs : (a.next+1#usize : Result Usize) ⦃ n => n.val=a.next.val+1 ⦄ := by
  apply UScalar.add_spec
  scalar_tac
 obtain ⟨n,hn,hval⟩ := WP.spec_imp_exists hs
 have same := Result.ok.inj (hn.symm.trans hnext)
 exact ⟨hb,by simpa only [same] using hval,hw⟩
#print axioms bound
#print axioms source
end XSc_QueryNext
