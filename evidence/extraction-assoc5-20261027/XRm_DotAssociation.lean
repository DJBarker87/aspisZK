import XRm_DotSites
import XRl_WideCanonical
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
namespace XRm_DotAssociation
theorem canonical_iff (e : XRk_Wide) :
    XRm_WideProducer.Canonical e ↔ XRl_WideCanonical.Canonical e := by
  simp only [XRm_WideProducer.Canonical,XRm_FieldCanonical.Q,XRm_FieldCanonical.C,
    XRm_FieldCanonical.M,XRl_WideCanonical.Canonical,XRk_CanonicalScalar.Canonical,and_assoc]

/-- Canonical-history laws for the actual three emitted push sites, fed by
the SAME accepted Prepared.new scratch. No arbitrary-history or native private
type premise supplies operand canonicality. Source/native P6 remains separate. -/
theorem prepared_tail {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (old scratch : Array XRk_Wide 29#usize) (prepared : verifier.Prepared)
    (prepare : verifier.Prepared.new D sem view hash old=ok (.Ok prepared,scratch))
    (q : Array U8 608#usize) (slot : Usize) (out : XRk_Wide)
    (run : fast_dots.four_dots_one q scratch slot=ok out) :
    ∃ (xs : List XRl_DotHistory.Input) (d : fast_pairing.EbyKDot),
      XRl_DotHistory.Reached xs d ∧ xs.length=3 ∧ d.count.val=3 ∧
      xs.length≤4096 ∧
      (∀ v ∈ xs, XRl_WideCanonical.Canonical v.1 ∧ XRk_CanonicalScalar.Canonical v.2) ∧
      ∃ ops, XRl_DotSums.Operands xs ops ∧ ∀ j : Fin 4,
        d.c0.sums.val[j.val]?.getD 0#u64=
          (ops.map (fun v => (v.1,v.2.2))).foldl (XRl_DotSums.cellStep j) 0#u64 ∧
        d.c1.sums.val[j.val]?.getD 0#u64=
          (ops.map (fun v => (v.2.1,v.2.2))).foldl (XRl_DotSums.cellStep j) 0#u64 := by
  have canonical := XRm_PowersCanonical.prepared D sem view hash old scratch prepared prepare
  obtain ⟨xs,d,history,size,wide,_⟩ := XRm_DotSites.tail q scratch slot out canonical run
  obtain ⟨count,bound,scalar,ops,hop,cells⟩ := XRl_DotAssociation.reached xs d history
  refine ⟨xs,d,history,size,count.trans size,bound,?_,ops,hop,cells⟩
  intro v member
  exact ⟨(canonical_iff v.1).mp (wide v member),scalar v member⟩
#print axioms canonical_iff
#print axioms prepared_tail
end XRm_DotAssociation
