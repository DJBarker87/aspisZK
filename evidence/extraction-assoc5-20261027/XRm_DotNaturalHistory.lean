import XRm_DotNoWrap
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRm_DotNaturalHistory
/-- Every reached history has ordinary, non-wrapping natural sums for all
four cells in both accumulators. The <=4096 bound is derived from Reached. -/
theorem reached (xs : List XRl_DotHistory.Input) (d : fast_pairing.EbyKDot)
    (history : XRl_DotHistory.Reached xs d) :
    ∃ ops, XRl_DotSums.Operands xs ops ∧ ops.length≤4096 ∧ ∀ j : Fin 4,
      (d.c0.sums.val[j.val]?.getD 0#u64).val=
        (ops.map (fun v => (v.1,v.2.2))).foldl (XRm_DotNoWrap.natStep j) 0 ∧
      (d.c1.sums.val[j.val]?.getD 0#u64).val=
        (ops.map (fun v => (v.2.1,v.2.2))).foldl (XRm_DotNoWrap.natStep j) 0 := by
  obtain ⟨count,bound,canonical,ops,hop,cells⟩ := XRl_DotAssociation.reached xs d history
  have len := XRm_DotNoWrap.operands_length xs ops hop
  have opBound : ops.length≤4096 := by omega
  refine ⟨ops,hop,opBound,?_⟩
  intro j
  have left := XRm_DotNoWrap.zero j (ops.map (fun v => (v.1,v.2.2))) (by simpa only [List.length_map] using opBound)
  have right := XRm_DotNoWrap.zero j (ops.map (fun v => (v.2.1,v.2.2))) (by simpa only [List.length_map] using opBound)
  exact ⟨(congrArg UScalar.val (cells j).1).trans left.1,
    (congrArg UScalar.val (cells j).2).trans right.1⟩
#print axioms reached
end XRm_DotNaturalHistory
