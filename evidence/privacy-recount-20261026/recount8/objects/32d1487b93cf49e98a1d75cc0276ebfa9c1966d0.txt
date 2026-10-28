import R1Z.PV_RunJoin_MergeComplete35
import R1Z.PV_RunJoin_MergeSum35
import R1Z.PV_RunJoin_SampleDomain34
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MergeActual35
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FieldData34 PV_RunJoin_MergeArray35
variable [ExternalTypes]

/-- The whole emitted merge at the ACTUAL round's assignments/count. Every
arithmetic side condition is discharged. The input array remains to be
identified with the native worker output and actual semantic oracle. -/
theorem complete (ops : ExternalFuns) (r : Usize) (hr : r.val<10) (es : Nat → Q)
    (he : ∀ j, j<(PV_RunJoin_SampleDomain34.count r).val → canonical (es j)) :
    ∃ out : Nat → Q,
      @host_sumcheck.merge_evaluations _ (ProverRwDictionaryTower.selected ops)
        (Array.to_slice (ProverCommitArray49.array (PV_RunJoin_SampleDomain34.count r)
          (fun j => core.result.Result.Ok (es j)))) (PV_RunJoin_SampleDomain34.assignments r) =
        .ok (.Ok (array out)) ∧
      (∀ k, k<28 → canonical (out k)) ∧
      ∀ k, value (out k)=∑ j ∈ Finset.range (PV_RunJoin_SampleDomain34.count r).val,
        if j/(PV_RunJoin_SampleDomain34.assignments r).val=k then value (es j) else 0 := by
  have ha := PV_RunJoin_SampleDomain34.assignments_bound r hr
  have hc := PV_RunJoin_SampleDomain34.count_value r hr
  obtain ⟨out,hout,hcanon,hm⟩ := PV_RunJoin_MergeComplete35.complete ops
    (PV_RunJoin_SampleDomain34.count r) (PV_RunJoin_SampleDomain34.assignments r) es
    (by omega) (Nat.ne_of_gt ha.1) (fun j hj => (Nat.div_lt_iff_lt_mul ha.1).mpr (by rw [hc] at hj;simpa only [Nat.mul_comm] using hj)) he
  refine ⟨out,hout,hcanon,?_⟩
  intro k
  have cell := congrFun hm k
  rw [PV_RunJoin_MergeSum35.cell,zero_add,PV_RunJoin_MergeSum35.sum] at cell
  simpa only [Nat.zero_add] using cell

#print axioms complete
end R1Z.PV_RunJoin_MergeActual35
