import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MergeComplete35
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FieldData34 PV_RunJoin_MergeArray35 PV_RunJoin_MergeFold35
variable [ExternalTypes]

theorem repeat_constant (q : Q) : Array.repeat 28#usize q = array (fun _ => q) := by
  apply Subtype.ext
  simp only [Array.repeat,array,ProverCommitArray49.array,List.ofFn_const]

theorem zero (ops : ExternalFuns) :
    @aspis_core.field.QM31.ZERO _ (ProverRwDictionaryTower.selected ops) =
      .ok (source ProverCommitSubfieldOps47.zero) := by
  change Result.ok (ProverRwDictionaryTower.fromQ AspisR1ProducerRelease47.field.QM31.ZERO) = _
  rw [ProverCommitQArray48.source_zero]
  rfl

/-- Complete emitted helper, with canonical source evaluation values. This
removes its initialization and merge-loop obligations; the actual worker map
and semantic-oracle law are still required at its caller. -/
theorem complete (ops : ExternalFuns) (count a : Usize) (es : Nat → Q)
    (small : count.val≤14336) (positive : a.val≠0)
    (samples : ∀ j, j<count.val → j/a.val<28)
    (he : ∀ j, j<count.val → canonical (es j)) :
    ∃ out : Nat → Q,
      @host_sumcheck.merge_evaluations _ (ProverRwDictionaryTower.selected ops)
        (Array.to_slice (ProverCommitArray49.array count (fun j => (core.result.Result.Ok (es j) : core.result.Result Q r1_wire.Error)))) a =
        .ok (.Ok (array out)) ∧
      (∀ k, k<28 → canonical (out k)) ∧
      (fun k => value (out k))=fold count.val (fun _ => 0) (fun j => value (es j)) a.val 0 := by
  obtain ⟨out,hout,hc,hm⟩ := PV_RunJoin_MergeLoop35.complete ops count.val count a 0#usize
    (fun _ => source ProverCommitSubfieldOps47.zero) es (by change 0+count.val=count.val;omega) small positive samples
    (fun _ _ => (canonical_source _).mpr ProverCommitSubfieldOps47.zero_canonical) he
  refine ⟨out,?_,hc,?_⟩
  · unfold host_sumcheck.merge_evaluations
    rw [zero]
    simp only [bind_tc_ok,repeat_constant]
    have len : Slice.len (Array.to_slice (ProverCommitArray49.array count
        (fun j => (core.result.Result.Ok (es j) : core.result.Result Q r1_wire.Error))))=count := by
      apply UScalar.eq_of_val_eq
      simp only [Slice.len,Array.to_slice,ProverCommitArray49.array,List.length_ofFn,Usize.ofNatCore_val_eq]
    rw [len,hout]
    rfl
  · simpa only [value_source,ProverCommitSubfieldOps47.zero_decode,
      show (0#usize).val=0 from rfl] using hm

#print axioms repeat_constant
#print axioms zero
#print axioms complete
end R1Z.PV_RunJoin_MergeComplete35
