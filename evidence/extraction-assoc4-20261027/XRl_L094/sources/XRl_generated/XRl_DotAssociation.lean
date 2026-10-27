import XRl_DotSums
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRl_DotAssociation
/-- Reached-history result with one shared operand sequence for BOTH dots and
every wrapping cell. Canonicality is derived for scalars only; the wide-value
producer invariant is deliberately not smuggled into the history predicate. -/
theorem reached (xs : List XRl_DotHistory.Input) (s : fast_pairing.EbyKDot)
    (history : XRl_DotHistory.Reached xs s) :
    s.count.val=xs.length ∧ xs.length≤4096 ∧
    (∀ v ∈ xs, XRk_CanonicalScalar.Canonical v.2) ∧
    ∃ ops, XRl_DotSums.Operands xs ops ∧ ∀ j : Fin 4,
      s.c0.sums.val[j.val]?.getD 0#u64 =
        (ops.map (fun v => (v.1,v.2.2))).foldl (XRl_DotSums.cellStep j) 0#u64 ∧
      s.c1.sums.val[j.val]?.getD 0#u64 =
        (ops.map (fun v => (v.2.1,v.2.2))).foldl (XRl_DotSums.cellStep j) 0#u64 := by
  have count := XRl_DotHistory.count xs s history
  obtain ⟨ops,hop,h0,h1⟩ := XRl_DotSums.factor xs s history
  refine ⟨count.1,count.2,XRl_DotHistory.canonical_scalars xs s history,ops,hop,?_⟩
  intro j
  exact ⟨XRl_DotSums.cells _ _ h0 j,XRl_DotSums.cells _ _ h1 j⟩
#print axioms reached
end XRl_DotAssociation
