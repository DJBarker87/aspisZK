import R1Z.PV_RunJoin_InterpolationLoop38
import R1Z.ProverCommitInterpolationModel48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InterpolationComplete38
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FieldData34 PV_RunJoin_MergeArray35 PV_RunJoin_AccPolynomial38
variable [ExternalTypes]

def zero : Q := PV_RunJoin_FieldData34.source ProverCommitSubfieldOps47.zero

theorem zero_poly : poly (fun _ => zero)=0 := by
  simpa only [poly,zero,old_source] using ProverCommitInterpolationOutput48.zero_poly

/-- Complete emitted interpolation Result, on arbitrary raw input cells.
The output is canonical and is exactly the Lagrange polynomial on the 28
source sample values. No terminal, worker, interpolation-success or desired
polynomial equation is a hypothesis. Native/deployment association stays P. -/
theorem interpolate (ops : ExternalFuns) (values : Nat → Q) :
    ∃ out : Nat → Q,
      @host_sumcheck.interpolate _ (ProverRwP6BodyCandidate.selected ops) (array values)=.ok (array out) ∧
      (∀ k, k<28 → canonical (out k)) ∧
      poly out=Lagrange.interpolate Finset.univ
        (fun j : Fin 28 => (j.val : AspisR1.ExtractedCurrentQM31Exact.QM31Exact))
        (fun j => value (values j.val)) := by
  have hz : @aspis_core.field.QM31.ZERO _ (ProverRwP6BodyCandidate.selected ops)=.ok zero := by
    change Result.ok (ProverRwDictionaryTower.fromQ AspisR1ProducerRelease47.field.QM31.ZERO)=_
    rw [AspisR1ProducerRelease47.field.QM31.ZERO]
    rfl
  have hc : ∀ k : Nat, k<28 → canonical zero := fun _ _ =>
    (canonical_source _).mpr ProverCommitSubfieldOps47.zero_canonical
  have ha : Array.repeat 28#usize zero=array (fun _ => zero) := by
    apply Subtype.ext
    simp only [Array.repeat,array,ProverCommitArray49.array,List.ofFn_const]
  obtain ⟨out,hout,hcan,hpoly⟩ := PV_RunJoin_InterpolationLoop38.complete ops values 28 0#usize
    (fun _ => zero) rfl hc
  refine ⟨out,?_,hcan,?_⟩
  · unfold host_sumcheck.interpolate
    rw [hz]
    simp only [bind_tc_ok,ha]
    exact hout
  · rw [hpoly,zero_poly,zero_add]
    exact ProverCommitInterpolationModel48.sum_model (fun k => old (values k))

#print axioms zero_poly
#print axioms interpolate
end R1Z.PV_RunJoin_InterpolationComplete38
