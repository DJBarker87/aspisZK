import R1Z.PV_RunJoin_MergeActual35
import R1Z.ProverRwP6BodyCandidate
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MergeInstall35
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FieldData34 PV_RunJoin_MergeArray35
variable [ExternalTypes]

/-- The actual candidate dictionary reaches exactly the discharged ZERO and
QM31-add entries. No irrelevant external callback replacement is assumed. -/
theorem dictionary (ops : ExternalFuns) :
    @host_sumcheck.merge_evaluations _ (ProverRwP6BodyCandidate.selected ops) =
      @host_sumcheck.merge_evaluations _ (ProverRwDictionaryTower.selected ops) := by
  unfold host_sumcheck.merge_evaluations host_sumcheck.merge_evaluations_loop
    host_sumcheck.merge_evaluations_loop.body
  rfl

theorem installed (ops : ExternalFuns) (r : Usize) (hr : r.val<10) (es : Nat → Q)
    (he : ∀ j, j<(PV_RunJoin_SampleDomain34.count r).val → canonical (es j)) :
    ∃ out : Nat → Q,
      @host_sumcheck.merge_evaluations _ (ProverRwP6BodyCandidate.selected ops)
        (Array.to_slice (ProverCommitArray49.array (PV_RunJoin_SampleDomain34.count r)
          (fun j => core.result.Result.Ok (es j)))) (PV_RunJoin_SampleDomain34.assignments r) =
        .ok (.Ok (array out)) ∧
      (∀ k, k<28 → canonical (out k)) ∧
      ∀ k, value (out k)=∑ j ∈ Finset.range (PV_RunJoin_SampleDomain34.count r).val,
        if j/(PV_RunJoin_SampleDomain34.assignments r).val=k then value (es j) else 0 := by
  rw [dictionary]
  exact PV_RunJoin_MergeActual35.complete ops r hr es he

#print axioms dictionary
#print axioms installed
end R1Z.PV_RunJoin_MergeInstall35
